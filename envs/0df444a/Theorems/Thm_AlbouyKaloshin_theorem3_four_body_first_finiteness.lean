-- Prove2me | Theorems.Thm_AlbouyKaloshin_theorem3_four_body_first_finiteness
-- name    : AlbouyKaloshin.theorem3_four_body_first_finiteness
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:27:13.344792+00:00
-- url     : https://prove2.me/theorems/a8b050f8-a765-44d0-835e-b6d0561acf20
-- title:
--   Theorem 3: four bodies, finiteness outside conditions (14), (16), (20)
-- statement:
--   Let $m_1,m_2,m_3,m_4>0$. Suppose there is **no** renumbering $\sigma$ of the four bodies for which the renumbered masses $\mu_i=m_{\sigma(i)}$ satisfy one of
--
--   1. condition (14): $\mu_1\mu_3=\mu_2\mu_4$;
--   2. condition (16): $\dfrac1{\sqrt{\mu_1}}=\dfrac1{\sqrt{\mu_2}}+\dfrac1{\sqrt{\mu_3}}$;
--   3. condition (20): $\mu_1^2(\mu_2+\mu_3)^4=\mu_2^3\mu_3^3$.
--
--   Then system (4) with $n=4$ has finitely many complex solutions, i.e. there are finitely many normalized central configurations of four bodies in the complex domain.
--
--   This is the paper's first four-body finiteness result, later sharpened by Theorem 4.
--
--   **Formalization Note** The paper lists (16) as three equations differing by the choice of the distinguished body; since a renumbering is allowed, the first form under all permutations is equivalent.
-- source:
--   A. Albouy and V. Kaloshin, Finiteness of central configurations of five bodies in the plane, Annals of Mathematics 176 (2012), no. 1, 535–588, https://doi.org/10.4007/annals.2012.176.1.10, p. 560, Theorem 3, with conditions (14) p. 558, (16) p. 559, (20) p. 560

import Mathlib
import Definitions.Def_AlbouyKaloshin_CentralConfigurations

namespace AlbouyKaloshin

theorem theorem3_four_body_first_finiteness (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (hcond : ¬ ∃ σ : Equiv.Perm (Fin 4),
      m (σ 0) * m (σ 2) = m (σ 1) * m (σ 3) ∨
      1 / Real.sqrt (m (σ 0)) = 1 / Real.sqrt (m (σ 1)) + 1 / Real.sqrt (m (σ 2)) ∨
      m (σ 0) ^ 2 * (m (σ 1) + m (σ 2)) ^ 4 = m (σ 1) ^ 3 * m (σ 2) ^ 3) :
    (NormalizedCC 4 (fun k => (m k : ℂ))).Finite := by sorry

end AlbouyKaloshin
