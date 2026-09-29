-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_loss_interpolation
-- name    : BanditAlgorithm.partial_monitoring_neighbour_loss_interpolation
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:32:33.206813+00:00
-- url     : https://prove2.me/theorems/946fd478-65ab-4b2a-8c48-9195cb10fc03
-- title:
--   Loss vectors incident to an edge interpolate its endpoint losses
-- statement:
--   Let $a,b$ be neighbouring actions and let $c$ be incident to their edge, meaning $c\in N_{ab}$. Then the loss vector of $c$ lies on the segment joining the endpoint loss vectors:
--
--   $$
--   \exists\alpha\in[0,1],\qquad
--   \ell_c=\alpha\ell_a+(1-\alpha)\ell_b.
--   $$
--
--   The endpoint cases include actions with the same loss vector as $a$ or $b$; the strict interior case is exactly Lemma 37.8(a). This identity yields Eq. (37.10) for the two perturbed environments.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), Lemma 37.8(a), printed pp. 484–485; applied in Theorem 37.12, Step 3, Eq. (37.10), printed p. 491.

import Definitions.Def_PartialMonitoringGame

theorem BanditAlgorithm.partial_monitoring_neighbour_loss_interpolation
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    (a b : Fin k) (hab : NeighbouringActions G a b) :
    ∀ c : Fin k, c ∈ pmNeighbourhood G a b →
      ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
        ∀ i : Fin d, G.L c i = α * G.L a i + (1 - α) * G.L b i := by sorry
