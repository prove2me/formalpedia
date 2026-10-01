-- Prove2me | Theorems.Thm_CandesTao_Decoding_theta_le_delta_le_theta_add_max
-- name    : CandesTao.Decoding.theta_le_delta_le_theta_add_max
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-30T22:08:19.780704+00:00
-- url     : https://prove2.me/theorems/3e068ca6-96d9-4788-836f-6898259d19a7
-- title:
--   Lemma 1.2: $\theta_{S,S'} \le \delta_{S+S'} \le \theta_{S,S'} + \max(\delta_S, \delta_{S'})$
-- statement:
--   Let $F$ be a real $p \times m$ matrix with restricted isometry constants $\delta_S$ and restricted orthogonality constants $\theta_{S,S'}$ (Definition 1.1). For all integers $S, S' \ge 1$ with $S + S' \le m$,
--   $$
--   \theta_{S,S'} \;\le\; \delta_{S+S'} \;\le\; \theta_{S,S'} + \max(\delta_S, \delta_{S'}).
--   $$
--
--   The lemma shows that the isometry constants $\delta$ alone control the orthogonality constants $\theta$, the cosine of the principal angle between the spans of two disjoint sparse sets of columns. This is why exact reconstruction can be guaranteed from knowledge of the $\delta$ numbers only: the hypothesis $\delta_S + \theta_{S,S} + \theta_{S,2S} < 1$ of Theorem 1.4 is implied by $\delta_S + \delta_{2S} + \delta_{3S} < 1$ and implies $\delta_{2S} < 1$.
--
--   **Formalization Note** The hypotheses $S, S' \ge 1$ and $S + S' \le m$ are the domain on which Definition 1.1 defines $\delta_{S+S'}$ and $\theta_{S,S'}$; the constants themselves are total functions of $S, S'$.
-- source:
--   Candès--Tao 2005, Decoding by Linear Programming, IEEE Trans. Inform. Theory 51(12):4203-4215, doi:10.1109/TIT.2005.858979; arXiv:math/0502327v1 (https://arxiv.org/abs/math/0502327), p. 5, Lemma 1.2 (proved in Section 2.3, pp. 12-13)

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry

namespace CandesTao.Decoding
theorem theta_le_delta_le_theta_add_max {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S S' : ℕ)
    (hS : 1 ≤ S) (hS' : 1 ≤ S') (hSS' : S + S' ≤ m) :
    restrictedOrthogonalityConst F S S' ≤ restrictedIsometryConst F (S + S') ∧
    restrictedIsometryConst F (S + S') ≤
      restrictedOrthogonalityConst F S S' +
        max (restrictedIsometryConst F S) (restrictedIsometryConst F S') := by sorry
end CandesTao.Decoding
