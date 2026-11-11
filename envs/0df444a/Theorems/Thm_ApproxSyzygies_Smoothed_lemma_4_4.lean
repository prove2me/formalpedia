-- Prove2me | Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_4
-- name    : ApproxSyzygies.Smoothed.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:02:55.500821+00:00
-- url     : https://prove2.me/theorems/83564b60-f27a-4d7a-bae6-7fcd4642e13b
-- title:
--   Lemma 4.4 — reduction to a linear correction: $\|v_i^{D_i}g_i+C_i(g)\|\le\pi_T(\tau,\|\tilde b\|)\|f\|$ with $C_i$ independent of $v_i$
-- statement:
--   Fix $T$. There is one real polynomial $\pi_T$ in two variables, depending only on $T$, with the following property. Split the variables as $x=(y,z)$ (in the paper, $z$ are the coordinates of a block $V\subseteq S^\perp$ and every polynomial is restricted to $S\oplus V$). Let $a_j\in\mathbb R[y,z]_{=d_j}$, $d_j\ge1$, $D_j\ge1$, $b_j=a_j^{D_j}$, $1\le t\le T$, fix $i\in[m]$, and write $a_i=c_i+v_i$ with $v_i\in\mathbb R[z]_{=d_i}$ pure in $z$. Let $\tilde b=(b_1,\dots,b_{i-1},c_i,b_{i+1},\dots,b_m)$. There is a linear map
--   $$C_i:\bigoplus_j\mathbb R[y]_{=t-d_jD_j}\to\mathbb R[y,z]_{=t},$$
--   determined by $\tilde b$ alone (so independent of $v_i$), such that whenever both $b$ and $\tilde b$ satisfy the kernel condition of Lemma 4.3 ($\ker M^{(s)}_p[0]=\mathcal K^{(s)}_p[0]$ for $0\le s<t$), with $\tau=\max_{p\in\{b,\tilde b\}}\max_{0\le s<t}\|W^{(s)}_p[0]\|_{op}$:
--   $$\|C_i\|_{op}\le\pi_T(\tau,\|\tilde b\|),\qquad \big\|v_i^{D_i}g_i+C_i(g)\big\|\le\pi_T(\tau,\|\tilde b\|)\,\|f\|$$
--   for every $h\in\bigoplus_j\mathbb R[y,z]_{=t-d_jD_j}$, where $f=\sum_jb_jh_j$ and $g_j=\Pi^\perp_{J_j}h_j[0]$. It isolates the fresh randomness $v_i$ from the rest, which enters only through a linear correction.
--
--   Differences from the source:
--   - reading: "$C_i$ ... independent of $v_i$" ($v_i$ the Gaussian perturbation on the $V$-variables) → $C_i$ is a function of $\tilde b$ alone, chosen before $a$ and $v_i$; reason: deterministic reading: in the proof $C_i$ is built from $\tilde b$ only, and $\tilde b$ does not involve $v_i$
--   - reading: the §4.4 set-up: $a_i=c_i+v_i$, $v_i$ the pure-$V$ Gaussian part, $c_i$ the rest; $t\in[T]$ → any split $a_i=c_i+v_i$ with $v_i\in\mathbb R[z]_{=d_i}$ (`liftZ v`), any homogeneous $a_j$ with $d_j,D_j\ge1$, $1\le t\le T$; variables `Y ⊕ Z` for $S\oplus V$; reason: the lemma is deterministic; the probabilistic origin of $v_i$ is used only later
--   - encoding: $C_i:\bigoplus_jJ_j^\perp\to\mathbb R[y,z]_{=t}$ → $C_i$ defined on all of $\bigoplus_j\mathbb R[y]_{=t-d_jD_j}$; reason: restricting gives the paper's map with the same norm bound, and $C_i\circ\Pi_{J^\perp}$ extends a map on $J^\perp$ with the same norm; $g\in J^\perp$
--   - encoding: $\pi_T$ "a polynomial that depends only on $T$", evaluated at $(\tau,\|\tilde b\|)$ → `π : MvPolynomial (Fin 2) ℝ` chosen after $T$ only, evaluated at `![τ, tupNorm b̃]`; reason: a real polynomial in two variables
--   - encoding: $v_i^{D_i}g_i$, a product of polynomials on disjoint variables → `ofPoly t (toPoly (liftZ v) ^ D i * toPoly (liftY (g i)))`, Bombieri norm in $\mathbb R[y,z]_{=t}$; reason: the product as a polynomial in $x=(y,z)$
--   - encoding: $\tilde b_i=a_i-v_i$ → `modGen d D i (toPoly (a i) - toPoly (liftZ v)) a`; reason: the modified family of §4.4
--   - encoding: coordinate split $x=(y,z)$, $\mathbb R^n=S\oplus S^\perp$ → variables indexed by `Y ⊕ Z`; $f[r]$ = `grade r f`, $f[0]$ as a polynomial in $y$ = `yPart f` ($z\mapsto0$); reason: a coordinate split is a partition of the variable set
--   - encoding: $\mathcal K^{(s)}_{p}[0]=\{k[0]:k\in\mathcal K^{(s)}_{p}\}$ → `koszul (yParts p) s`, the Koszul syzygy space of $p[0]$ over $\mathbb R[y]$; reason: the page states the equivalence (p. 19: "Equivalently, this is the Koszul syzygy space of $b[0]$ over $\mathbb R[y]$")
--   - encoding: $\tau=\max_{0\le s<t}\|W^{(s)}_p[0]\|_{op}$, $W$ the Moore–Penrose pseudoinverse → `tauOf p₀ t` = $\max_{s<t}$ `pinvNorm` $(M^{(s)}_{p[0]})$, where `pinvNorm M` is the least $\tau\ge0$ with $\|u\|\le\tau\|Mu\|$ for all $u\perp\ker M$; reason: that least $\tau$ is exactly $\|W\|_{op}$ ($1/\sigma^+_{\min}(M)$, or $0$ for $M=0$); no pseudoinverse needs to be built
--   - encoding: $\mathbb R[x]_{=d}$ with the Bombieri inner product; $\mathbb R[x]_{=d}=\{0\}$ for $d<0$ → `Hom σ d` = Euclidean space on the multi-indices $|\alpha|=d$ (empty for $d<0$), read as $\sum_\alpha p_\alpha\sqrt{d!/\alpha!}\,x^\alpha$ by `toPoly`; `ofPoly d f` reads a polynomial back; integer degrees; reason: the Bombieri-orthonormal coordinates make the Bombieri norm the Euclidean norm (p. 17); integer degrees give the zero space for negative degree with no truncated subtraction
-- source:
--   Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, Approximate Syzygies of Smoothed Polynomials and Applications, STOC 2027 submission (manuscript sha256 9c17d04e…), p. 30, Lemma 4.4

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Bombieri

open MvPolynomial

namespace ApproxSyzygies.Smoothed

/-- Lemma 4.4 (p. 30): reduction to a linear correction. For every `T` there is one real polynomial
`π_T` in two variables such that: for a coordinate split `x = (y, z)`, homogeneous
`a_j ∈ ℝ[x]_{=d_j}` (`d_j ≥ 1`), `b_j = a_j^{D_j}` (`D_j ≥ 1`), `1 ≤ t ≤ T`, an index `i` and a split
`a_i = c_i + v_i` with `v_i ∈ ℝ[z]_{=d_i}` pure in `z`, the modified family
`b̃ = (b_1, …, c_i, …, b_m)`: there is a linear map `C_i : ⨁_j ℝ[y]_{=t − d_j D_j} → ℝ[y, z]_{=t}`, a
function of `b̃` alone (hence independent of `v_i`), such that whenever `b[0]` and `b̃[0]` satisfy the
kernel condition of Lemma 4.3, with `τ = max_{p ∈ {b, b̃}} max_{0 ≤ s < t} ‖W_p^{(s)}[0]‖_op`:
`‖C_i‖_op ≤ π_T(τ, ‖b̃‖)` and every `h ∈ ⨁_j ℝ[y, z]_{=t − d_j D_j}` satisfies
`‖v_i^{D_i} g_i + C_i(g)‖ ≤ π_T(τ, ‖b̃‖) ‖f‖`, `f = ∑_j b_j h_j`, `g_j = Π^⊥_{J_j} h_j[0]`. -/
theorem lemma_4_4 (T : ℕ) :
    ∃ π : MvPolynomial (Fin 2) ℝ,
      ∀ {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}
        (d D : Fin m → ℕ), (∀ j, 1 ≤ d j) → (∀ j, 1 ≤ D j) →
        ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ i : Fin m,
        ∃ Cmap : (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
            (Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)) →L[ℝ] Hom (Y ⊕ Z) (t : ℤ)),
        ∀ (a : ∀ j, Hom (Y ⊕ Z) (d j : ℤ)) (v : Hom Z (d i : ℤ)),
          KernelCond (yParts fun j => powHom (a j) (D j)) t →
          KernelCond (yParts (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)) t →
          ‖Cmap (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)‖ ≤
              eval ![max (tauOf (yParts fun j => powHom (a j) (D j)) t)
                      (tauOf (yParts (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)) t),
                    tupNorm (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)] π ∧
            ∀ h : Tup (Y ⊕ Z) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)),
              ‖ofPoly (t : ℤ) (toPoly (liftZ (Y := Y) v) ^ D i *
                    toPoly (liftY (Z := Z) (gVec d D t (yParts a) (yPartTup h) i))) +
                  Cmap (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)
                    (gVec d D t (yParts a) (yPartTup h))‖ ≤
                eval ![max (tauOf (yParts fun j => powHom (a j) (D j)) t)
                        (tauOf (yParts (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)) t),
                      tupNorm (modGen d D i (toPoly (a i) - toPoly (liftZ (Y := Y) v)) a)] π *
                  ‖mulMap (fun j => powHom (a j) (D j)) (t : ℤ) h‖ := by sorry

end ApproxSyzygies.Smoothed
