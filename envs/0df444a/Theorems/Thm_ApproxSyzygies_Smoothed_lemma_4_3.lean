-- Prove2me | Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_3
-- name    : ApproxSyzygies.Smoothed.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:02:50.90289+00:00
-- url     : https://prove2.me/theorems/3331f748-5ccb-48ba-be6a-90ef77d383d1
-- title:
--   Lemma 4.3 — substitution: $h[r]=k[r]+F_r(f[0{:}r])+H_r(h_0)$ with explicit operator-norm bounds
-- statement:
--   Split the variables as $x=(y,z)$ and let $p=(p_1,\dots,p_m)$, $p_i\in\mathbb R[x]_{=e_i}$, $e_i\ge1$, be homogeneous generators. Fix $T$, an output degree $t\le T$ and a final row $0\le R\le t$. Suppose $\ker M^{(s)}_p[0]=\mathcal K^{(s)}_p[0]$ for every $0\le s<t$, and let $\tau=\max_{0\le s<t}\|W^{(s)}_p[0]\|_{op}$. Then there are linear maps $F_r,H_r$ ($0\le r\le R$), depending only on $p[0:r]$, with
--   $$\|F_r\|_{op},\ \|H_r\|_{op}\ \le\ 1+2^{T/2}\tau\cdot\max\Big\{\big(1+2^{T/2}\tau\|p\|\big)^{R-1},\ \|p\|\big(1+2^{T/2}\tau\|p\|\big)^{R-1}\Big\},$$
--   such that for every $h\in\bigoplus_i\mathbb R[x]_{=t-e_i}$ with $f=p^\top h$ and every target pure-$y$ part $h_0\in h[0]+\mathcal K^{(t)}_p[0]$ there is $k\in\mathcal K^{(t)}_p$ with $k[0]=h[0]-h_0$ and
--   $$h[r]=k[r]+F_r(f[0:r])+H_r(h_0)\qquad(0\le r\le R).$$
--   The lemma propagates the bound on $h[0]$ to every $z$-degree layer of $h$.
--
--   Differences from the source:
--   - reading: $T$ (the "fixed upper bound" of the output degree, Table 1, p. 20; not repeated in the lemma) → hypothesis $t\le T$; reason: standing assumption of §4 ($t\in[T]$); the factor $2^{T/2}$ bounds $\binom tR^{1/2}$ only when $t\le T$
--   - encoding: maps $F_r,H_r$ "depending only on $p[0:r]$" → $F_r,H_r$ are functions of $p$, chosen before $p$, with $F_r(p)=F_r(p')$ and $H_r(p)=H_r(p')$ whenever $p_i[r']=p'_i[r']$ for all $i$ and $r'\le r$; reason: makes the dependence explicit
--   - encoding: pure-$y$ parts $h[0]$, $k[0]$, $h_0$ → tuples of polynomials in $y$ (`yPartTup`, `Tup Y`); reason: a pure-$y$ polynomial and the same polynomial over $y$ have the same Bombieri norm
--   - encoding: $f[0:r]$ and the exponent $R-1$ → the tuple $(f[0],\dots,f[r])$ with the product norm (`gradeSeg`); an integer power `^ ((R : ℤ) - 1)`; reason: the layers are orthogonal, so the product norm is $\|f[0]+\dots+f[r]\|$; at $R=0$ the exponent is $-1$, as printed
--   - encoding: coordinate split $x=(y,z)$, $\mathbb R^n=S\oplus S^\perp$ → variables indexed by `Y ⊕ Z`; $f[r]$ = `grade r f`, $f[0]$ as a polynomial in $y$ = `yPart f` ($z\mapsto0$); reason: a coordinate split is a partition of the variable set
--   - encoding: $\mathcal K^{(s)}_{p}[0]=\{k[0]:k\in\mathcal K^{(s)}_{p}\}$ → `koszul (yParts p) s`, the Koszul syzygy space of $p[0]$ over $\mathbb R[y]$; reason: the page states the equivalence (p. 19: "Equivalently, this is the Koszul syzygy space of $b[0]$ over $\mathbb R[y]$")
--   - encoding: $\tau=\max_{0\le s<t}\|W^{(s)}_p[0]\|_{op}$, $W$ the Moore–Penrose pseudoinverse → `tauOf p₀ t` = $\max_{s<t}$ `pinvNorm` $(M^{(s)}_{p[0]})$, where `pinvNorm M` is the least $\tau\ge0$ with $\|u\|\le\tau\|Mu\|$ for all $u\perp\ker M$; reason: that least $\tau$ is exactly $\|W\|_{op}$ ($1/\sigma^+_{\min}(M)$, or $0$ for $M=0$); no pseudoinverse needs to be built
--   - encoding: $\mathbb R[x]_{=d}$ with the Bombieri inner product; $\mathbb R[x]_{=d}=\{0\}$ for $d<0$ → `Hom σ d` = Euclidean space on the multi-indices $|\alpha|=d$ (empty for $d<0$), read as $\sum_\alpha p_\alpha\sqrt{d!/\alpha!}\,x^\alpha$ by `toPoly`; `ofPoly d f` reads a polynomial back; integer degrees; reason: the Bombieri-orthonormal coordinates make the Bombieri norm the Euclidean norm (p. 17); integer degrees give the zero space for negative degree with no truncated subtraction
-- source:
--   Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, Approximate Syzygies of Smoothed Polynomials and Applications, STOC 2027 submission (manuscript sha256 9c17d04e…), pp. 24-25, Lemma 4.3

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Bombieri

namespace ApproxSyzygies.Smoothed

/-- Lemma 4.3 (pp. 24–25): substitution. Coordinate split `x = (y, z)`; positive-degree generators
`p_i ∈ ℝ[x]_{=e_i}`; output degree `t ≤ T`; final row `0 ≤ R ≤ t`. There are linear maps `F_r`,
`H_r` (`r ≤ R`), functions of `p` that depend only on `p[0 : r]`, such that whenever
`ker M_p^{(s)}[0] = K_p^{(s)}[0]` for all `0 ≤ s < t`, with `τ = max_{0 ≤ s < t} ‖W_p^{(s)}[0]‖_op`:
`‖F_r‖_op, ‖H_r‖_op ≤ 1 + 2^{T/2} τ max{(1 + 2^{T/2} τ ‖p‖)^{R−1}, ‖p‖ (1 + 2^{T/2} τ ‖p‖)^{R−1}}`, and
for every `h ∈ ⨁_i ℝ[x]_{=t − e_i}` with `f = pᵀh` and every `h₀ ∈ h[0] + K_p^{(t)}[0]` there is
`k ∈ K_p^{(t)}` with `k[0] = h[0] − h₀` and `h[r] = k[r] + F_r(f[0 : r]) + H_r(h₀)` for `r ≤ R`. -/
theorem lemma_4_3 (T : ℕ) {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {m : ℕ} (e : Fin m → ℕ) (he : ∀ i, 1 ≤ e i) (t : ℕ) (htT : t ≤ T) (R : ℕ) (hR : R ≤ t) :
    ∃ F : (r : ℕ) → (∀ i, Hom (Y ⊕ Z) (e i : ℤ)) →
        ((PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) →L[ℝ]
          Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ))),
    ∃ H : (r : ℕ) → (∀ i, Hom (Y ⊕ Z) (e i : ℤ)) →
        (Tup Y (fun i => (t : ℤ) - (e i : ℤ)) →L[ℝ] Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ))),
      (∀ r, r ≤ R → ∀ p p' : ∀ i, Hom (Y ⊕ Z) (e i : ℤ),
          (∀ r', r' ≤ r → ∀ i, grade r' (p i) = grade r' (p' i)) →
          F r p = F r p' ∧ H r p = H r p') ∧
      ∀ p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ), KernelCond (yParts p) t →
        (∀ r, r ≤ R →
          ‖F r p‖ ≤ 1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t *
              max ((1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))
                (tupNorm p *
                  (1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1)) ∧
          ‖H r p‖ ≤ 1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t *
              max ((1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))
                (tupNorm p *
                  (1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))) ∧
        ∀ (h : Tup (Y ⊕ Z) (fun i => (t : ℤ) - (e i : ℤ))) (h₀ : Tup Y (fun i => (t : ℤ) - (e i : ℤ))),
          h₀ - yPartTup h ∈ koszul (yParts p) (t : ℤ) →
          ∃ k ∈ koszul p (t : ℤ), yPartTup k = yPartTup h - h₀ ∧
            ∀ r, r ≤ R →
              gradeTup r h = gradeTup r k + F r p (gradeSeg r (mulMap p (t : ℤ) h)) + H r p h₀ := by sorry

end ApproxSyzygies.Smoothed
