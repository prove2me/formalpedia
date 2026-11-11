-- Prove2me | Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_2
-- name    : ApproxSyzygies.Smoothed.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:02:59.27781+00:00
-- url     : https://prove2.me/theorems/cd3720d2-b282-4d4e-b32e-7850328592f3
-- title:
--   Lemma 4.2 — reconstructing $h[0]$: $h[0]=k_0+L_1(g)+L_2(f[0])$ with $\|L_1\|\le1+\tau\|b[0]\|$, $\|L_2\|\le\tau$
-- statement:
--   Split the variables as $x=(y,z)$. Let $a_i\in\mathbb R[x]_{=d_i}$ be homogeneous with $d_i\ge1$, $D_i\ge1$, $b_i=a_i^{D_i}$, and fix an output degree $t\ge1$. Write $b[0]$ for the pure-$y$ parts, $M^{(s)}_b[0]:u\mapsto\sum_ib_i[0]u_i$ over $\mathbb R[y]$, $W^{(s)}_b[0]$ its Moore–Penrose pseudoinverse, $\tau=\max_{0\le s<t}\|W^{(s)}_b[0]\|_{op}$, $J_i=\langle b_1[0],\dots,b_{i-1}[0],a_i[0],b_{i+1}[0],\dots,b_m[0]\rangle_{t-d_iD_i}\subseteq\mathbb R[y]_{=t-d_iD_i}$, and for $h\in\bigoplus_i\mathbb R[x]_{=t-d_iD_i}$ put $f=\sum_ib_ih_i$ and $g_i=\Pi^\perp_{J_i}h_i[0]$.
--
--   There are linear maps $L_1,L_2$ that depend only on $b[0]$ such that, if $\ker M^{(t-1)}_b[0]=\mathcal K^{(t-1)}_b[0]$, then $\|L_1\|_{op}\le1+\tau\|b[0]\|$, $\|L_2\|_{op}\le\tau$, and every $h$ satisfies
--   $$h[0]=k_0+L_1(g)+L_2(f[0])\qquad\text{for some }k_0\in\mathcal K^{(t)}_b[0].$$
--   This is the first step of the induction on $t$ in the proof of Theorem 4.1: modulo Koszul syzygies, the pure-$y$ part of $h$ is a bounded linear function of the output and of the "important part" $g$.
--
--   Differences from the source:
--   - reading: "In the setting of Theorem 4.1" (smoothed random $a_i$) → every homogeneous $a_i\in\mathbb R[x]_{=d_i}$ with $d_i\ge1$, $D_i\ge1$, $t\ge1$; no probability; reason: the lemma and its proof are deterministic; the setting supplies only $b_i=a_i^{D_i}$, positive degrees and $t\in[T]$
--   - encoding: linear maps $L_1,L_2$ depending only on $b[0]$ → $L_1,L_2$ are functions of the tuple $b[0]$, chosen before $Z$, $a$ and $h$; reason: makes "depending only on $b[0]$" explicit
--   - encoding: coordinate split $x=(y,z)$, $\mathbb R^n=S\oplus S^\perp$ → variables indexed by `Y ⊕ Z`; $f[r]$ = `grade r f`, $f[0]$ as a polynomial in $y$ = `yPart f` ($z\mapsto0$); reason: a coordinate split is a partition of the variable set
--   - encoding: $\mathcal K^{(s)}_{p}[0]=\{k[0]:k\in\mathcal K^{(s)}_{p}\}$ → `koszul (yParts p) s`, the Koszul syzygy space of $p[0]$ over $\mathbb R[y]$; reason: the page states the equivalence (p. 19: "Equivalently, this is the Koszul syzygy space of $b[0]$ over $\mathbb R[y]$")
--   - encoding: $\tau=\max_{0\le s<t}\|W^{(s)}_p[0]\|_{op}$, $W$ the Moore–Penrose pseudoinverse → `tauOf p₀ t` = $\max_{s<t}$ `pinvNorm` $(M^{(s)}_{p[0]})$, where `pinvNorm M` is the least $\tau\ge0$ with $\|u\|\le\tau\|Mu\|$ for all $u\perp\ker M$; reason: that least $\tau$ is exactly $\|W\|_{op}$ ($1/\sigma^+_{\min}(M)$, or $0$ for $M=0$); no pseudoinverse needs to be built
--   - encoding: $\mathbb R[x]_{=d}$ with the Bombieri inner product; $\mathbb R[x]_{=d}=\{0\}$ for $d<0$ → `Hom σ d` = Euclidean space on the multi-indices $|\alpha|=d$ (empty for $d<0$), read as $\sum_\alpha p_\alpha\sqrt{d!/\alpha!}\,x^\alpha$ by `toPoly`; `ofPoly d f` reads a polynomial back; integer degrees; reason: the Bombieri-orthonormal coordinates make the Bombieri norm the Euclidean norm (p. 17); integer degrees give the zero space for negative degree with no truncated subtraction
-- source:
--   Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, Approximate Syzygies of Smoothed Polynomials and Applications, STOC 2027 submission (manuscript sha256 9c17d04e…), p. 21, Lemma 4.2

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Bombieri

namespace ApproxSyzygies.Smoothed

/-- Lemma 4.2 (p. 21): reconstructing `h[0]`. Coordinate split `x = (y, z)`; homogeneous
`a_i ∈ ℝ[x]_{=d_i}` (`d_i ≥ 1`), `b_i = a_i^{D_i}` (`D_i ≥ 1`), output degree `t ≥ 1`. There are linear
maps `L₁, L₂`, functions of `b[0]` alone, such that whenever `ker M_b^{(t−1)}[0] = K_b^{(t−1)}[0]`:
`‖L₁‖_op ≤ 1 + τ ‖b[0]‖`, `‖L₂‖_op ≤ τ` with `τ = max_{0 ≤ s < t} ‖W_b^{(s)}[0]‖_op`, and every
`h ∈ ⨁_i ℝ[x]_{=t − d_i D_i}` satisfies `h[0] = k₀ + L₁(g) + L₂(f[0])` for some
`k₀ ∈ K_b^{(t)}[0]`, where `f = ∑_i b_i h_i` and `g_i = Π^⊥_{J_i} h_i[0]`. -/
theorem lemma_4_2 {Y : Type} [Fintype Y] [DecidableEq Y] {m : ℕ} (d D : Fin m → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hD : ∀ i, 1 ≤ D i) (t : ℕ) (ht : 1 ≤ t) :
    ∃ L₁ : (∀ i, Hom Y ((d i : ℤ) * (D i : ℤ))) →
        (Tup Y (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ)) →L[ℝ]
          Tup Y (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ))),
    ∃ L₂ : (∀ i, Hom Y ((d i : ℤ) * (D i : ℤ))) →
        (Hom Y (t : ℤ) →L[ℝ] Tup Y (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ))),
    ∀ (Z : Type) [Fintype Z] [DecidableEq Z] (a : ∀ i, Hom (Y ⊕ Z) (d i : ℤ)),
      (LinearMap.ker (mulMap (yParts fun i => powHom (a i) (D i)) ((t : ℤ) - 1)) :
          Set (Tup Y (fun i => (t : ℤ) - 1 - (d i : ℤ) * (D i : ℤ)))) =
        koszul (yParts fun i => powHom (a i) (D i)) ((t : ℤ) - 1) →
      ‖L₁ (yParts fun i => powHom (a i) (D i))‖ ≤
          1 + tauOf (yParts fun i => powHom (a i) (D i)) t *
            tupNorm (yParts fun i => powHom (a i) (D i)) ∧
        ‖L₂ (yParts fun i => powHom (a i) (D i))‖ ≤
          tauOf (yParts fun i => powHom (a i) (D i)) t ∧
        ∀ h : Tup (Y ⊕ Z) (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ)),
          ∃ k₀ ∈ koszul (yParts fun i => powHom (a i) (D i)) (t : ℤ),
            yPartTup h = k₀ +
              L₁ (yParts fun i => powHom (a i) (D i)) (gVec d D t (yParts a) (yPartTup h)) +
              L₂ (yParts fun i => powHom (a i) (D i))
                (yPart (mulMap (fun i => powHom (a i) (D i)) (t : ℤ) h)) := by sorry

end ApproxSyzygies.Smoothed
