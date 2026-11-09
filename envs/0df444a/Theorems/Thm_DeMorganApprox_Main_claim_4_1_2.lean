-- Prove2me | Theorems.Thm_DeMorganApprox_Main_claim_4_1_2
-- name    : DeMorganApprox.Main.claim_4_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:56.695737+00:00
-- url     : https://prove2.me/theorems/83bd0f53-68b8-44e8-b134-1924ee35c1dd
-- title:
--   Claim 4.1.2 — the Chebyshev filter Ψ has coefficient sum Σⱼ |αⱼ| ≤ 2^{O(S)}
-- statement:
--   Let $\varepsilon=\frac1{1000\,c_{\rm norm}S}$, $d=\lceil c_{\rm cheb}/\varepsilon\rceil$, and let $\Psi(t)=\Phi(t)^2=\sum_{j=0}^{\deg\Psi}\alpha_jt^j$ be the Chebyshev filter of the proof of Lemma 4.1, where
--   $$\Phi(t)=\frac{T_d\!\left(1+\frac{2(\varepsilon^2-t^2)}{1-\varepsilon^2}\right)}{T_d\!\left(1+\frac{2\varepsilon^2}{1-\varepsilon^2}\right)} .$$
--   Then
--   $$\sum_{j=0}^{\deg\Psi}|\alpha_j|\le2^{O(S)},$$
--   with a constant depending only on $c_{\rm norm}$ and $c_{\rm cheb}$, uniformly in $S\ge1$.
--
--   This is the only exponential loss in the coefficient accounting of Lemma 4.1.
--
--   Differences from the source:
--   - generalization: the proof's fixed absolute constants c_norm (sufficiently large) and c_cheb (large enough) → every c_norm ≥ 1 and every c_cheb > 0, with K depending on them; reason: the statement specializes to the proof's constants
--   - reading: 2^{O(S)} → ∃ K chosen before S with Σⱼ |αⱼ| ≤ 2^{K·S} for every S ≥ 1; reason: the O-constant may depend on the absolute constants c_norm and c_cheb only
--   - encoding: T_d, d = ⌈c_cheb/ε⌉, and the sum over j = 0, …, deg Ψ → Polynomial.Chebyshev.T ℝ at the integer index d = ⌈c_cheb/ε⌉₊, and the sum over Finset.range (natDegree Ψ + 1) of |coeff j|; reason: Mathlib's Chebyshev polynomials satisfy T_d(cos α) = cos(dα); the same coefficients
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Claim 4.1.2, PDF p. 16 (printed p. 14), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; ε on PDF p. 13, d and Φ on PDF p. 14

import Mathlib
import Definitions.Def_DeMorganApprox_Main_Extraction

namespace DeMorganApprox.Main

/-- Claim 4.1.2, PDF p. 16 (printed p. 14): the coefficients `αⱼ` of `Ψ` satisfy
`Σⱼ |αⱼ| ≤ 2^{O(S)}`, with `ε = 1/(1000 c_norm S)` and `d = ⌈c_cheb/ε⌉`. -/
theorem claim_4_1_2 (cnorm ccheb : ℝ) (hcnorm : 1 ≤ cnorm) (hccheb : 0 < ccheb) :
    ∃ K : ℝ, ∀ S : ℝ, 1 ≤ S →
      ∑ j ∈ Finset.range
          ((chebFilterSq (filterEps cnorm S) (filterDeg ccheb (filterEps cnorm S))).natDegree + 1),
        |(chebFilterSq (filterEps cnorm S) (filterDeg ccheb (filterEps cnorm S))).coeff j| ≤
        (2 : ℝ) ^ (K * S) := by sorry

end DeMorganApprox.Main
