-- Prove2me | Theorems.Thm_DQI_Semicircle_lemma_9_2
-- name    : DQI.Semicircle.lemma_9_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:19.882669+00:00
-- url     : https://prove2.me/theorems/161a6ed3-f26c-4ad2-9ce8-7db4e83b3c1b
-- title:
--   Lemma 9.2, pp. 26–27 — if 2ℓ + 1 < d⊥ then ⟨s^(m,ℓ)⟩ = mr/p + (√(r(p − r))/p) wᵀA^(m,ℓ,d)w
-- statement:
--   Let $p$ be prime, $m>n\ge1$, $B\in\mathbb F_p^{m\times n}$, and $|F_i|=r$ for all $i$ with $1\le r\le p-1$. Let $\ell\ge0$ and $\mathbf w=(w_0,\dots,w_\ell)\in\mathbb R^{\ell+1}$, and consider the DQI state with amplitudes
--   $$a_{\mathbf w}(\mathbf x)=\sum_{k=0}^\ell w_k\frac{P^{(k)}(g_1(\mathbf b_1\cdot\mathbf x),\dots,g_m(\mathbf b_m\cdot\mathbf x))}{\sqrt{p^{n-k}\binom mk}},$$
--   normalized so that $\sum_{\mathbf x}a_{\mathbf w}(\mathbf x)^2=1$. If $2\ell+1<d^\perp$, the expected number of satisfied constraints upon measuring this state is
--   $$\langle s^{(m,\ell)}\rangle=\sum_{\mathbf x}a_{\mathbf w}(\mathbf x)^2s(\mathbf x)=\frac{mr}{p}+\frac{\sqrt{r(p-r)}}{p}\,\mathbf w^{T}A^{(m,\ell,d)}\mathbf w,\qquad d=\frac{p-2r}{\sqrt{r(p-r)}},$$
--   where $A^{(m,\ell,d)}$ is the tridiagonal matrix with diagonal $0,d,\dots,\ell d$ and off-diagonal $a_k=\sqrt{k(m-k+1)}$.
--
--   This reduces the optimization over polynomials to a Rayleigh quotient of an explicit $(\ell+1)\times(\ell+1)$ matrix.
--
--   **Formalization Note** The page writes the decomposition as $\sum_kw_kP^{(k)}(f_1,\dots,f_m)/\sqrt{p^{n-k}\binom mk}$; with this normalization the variables must be the rescaled $g_i$ of (44)–(46), §8.2.1 (with the $f_i$ the formula is false for $p>2$), and the statement uses the $g_i$. The polynomial $P$ enters only through $\mathbf w$, so the statement quantifies over $\mathbf w$; every such state is $|P(f)\rangle$ for a degree-$\le\ell$ polynomial $P$ and conversely (Lemma A.1).
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, pp. 26–27, Lemma 9.2, (69)–(70)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- Lemma 9.2, pp. 26–27, (69)–(70), with the decomposition in the `g_i` of (44)–(46). -/
theorem lemma_9_2 (p : ℕ) [Fact p.Prime] (m n : ℕ) (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p)
    (hnm : n < m) (hn : 0 < n) (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ)
    (hnorm : ∑ x, ampl B F ℓ w x ^ 2 = 1) (hdist : DistGt B (2 * ℓ + 1)) :
    expSat B F (ampl B F ℓ w) =
      (m : ℝ) * r / p + Real.sqrt (r * ((p : ℝ) - r)) / p * (w ⬝ᵥ (Atri m ℓ (dparOf p r)).mulVec w) := by sorry

end DQI.Semicircle
