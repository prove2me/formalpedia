-- Prove2me | Theorems.Thm_BipColorHard_lemma_34
-- name    : BipColorHard.lemma_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:12.758703+00:00
-- url     : https://prove2.me/theorems/3a22515f-7936-425a-bc1b-3840067f4482
-- title:
--   Lemma 34 — nondegeneracy of the global maxima of $\Phi$
-- statement:
--   Let $q=2k+1\ge5$, $d=q$, $p=(d+1)/d$. At every global maximum $(P,R)$ of $\Phi$, normalized so that both coordinate sums equal one, the Hessian of $\Phi$ is negative definite on
--   $$T_0=\Big\{(u,v):\sum_iu_i=\sum_iv_i=0\Big\}.$$
--
--   This nondegeneracy is a hypothesis of the finite-port theorem.
--
--   Differences from the source:
--   - encoding: global maximum of $\Phi$, normalized → a phase: a normalized maximizer of $L$; reason: $\Phi=(d+1)\log L$ is increasing in $L$
--   - encoding: negative definite Hessian → the restriction of the function to $(P,R)+T_0$ is twice continuously differentiable at $(P,R)$ with negative second derivative in every nonzero direction of $T_0$; reason: the Hessian is a quadratic form on $T_0$ of a function smooth near the pair
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 34, p.42 (PDF p.44)

import Definitions.Def_BipColorHard_Objective

set_option autoImplicit false

namespace BipColorHard

/-- **Lemma 34**, p.42 (PDF p.44), manuscript sha256 78a66d1f…. Range of §7: `q = 2k + 1 ≥ 5`, `d = q`,
`p = (d + 1)/d`. At every global maximum of `Φ`, normalized so that both coordinate sums are one, the Hessian of `Φ` is
negative definite on `T₀`.

**Formalization Note.** `Φ = (d + 1) log L`, so the normalized global maxima of `Φ` are the phases: the maximizers of `L`
over nonzero nonnegative vectors, normalized. -/
theorem lemma_34 (k : ℕ) (hk : 2 ≤ k) (P R : Fin (2 * k + 1) → ℝ)
    (hmax : IsPhase (((2 * k + 1 : ℕ) + 1 : ℝ) / (2 * k + 1 : ℕ)) P R) :
    HessNegDefOnT0 (objPhi (2 * k + 1)) P R := by sorry

end BipColorHard
