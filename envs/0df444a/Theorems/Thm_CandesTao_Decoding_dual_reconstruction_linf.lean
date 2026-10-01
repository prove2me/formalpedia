-- Prove2me | Theorems.Thm_CandesTao_Decoding_dual_reconstruction_linf
-- name    : CandesTao.Decoding.dual_reconstruction_linf
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-30T22:22:29.791498+00:00
-- url     : https://prove2.me/theorems/c71dfaee-bc6a-4b24-a88a-6e5faf910ec7
-- title:
--   Lemma 2.2: dual sparse reconstruction property, $\ell^\infty$ version
-- statement:
--   Let $F$ be a real $p \times m$ matrix with columns $v_1, \dots, v_m$ spanning $H$. Let $S \ge 1$ be such that $\delta_S + \theta_{S,2S} < 1$, and let $c$ be a real vector supported on $T \subseteq \{1, \dots, m\}$ with $|T| \le S$. Then there exists a vector $w \in H$ such that $\langle w, v_j \rangle = c_j$ for all $j \in T$, and
--   $$
--   |\langle w, v_j \rangle| \le \frac{\theta_{S,S}}{(1 - \delta_S - \theta_{S,2S})\sqrt{S}} \, \|c\| \quad \text{for all } j \notin T
--   $$
--   (equation (2.4)).
--
--   Applied to the sign vector of $c$ on $T$, this produces the dual vector $w$ with $\langle w, v_j \rangle = \operatorname{sgn}(c_j)$ on $T$ and $|\langle w, v_j \rangle| < 1$ off $T$ whenever $\delta_S + \theta_{S,S} + \theta_{S,2S} < 1$; Theorem 1.4 follows from it by the duality argument of Section 2.2.
--
--   **Formalization Note** The constants are transcribed exactly as printed in (2.4). The mission description ("Difficulty") records a caveat about how the paper's proof arrives at these constants. The hypothesis $3S \le m$ is the domain on which Definition 1.1 defines $\theta_{S,2S}$.
-- source:
--   Candès--Tao 2005, Decoding by Linear Programming, IEEE Trans. Inform. Theory 51(12):4203-4215, doi:10.1109/TIT.2005.858979; arXiv:math/0502327v1 (https://arxiv.org/abs/math/0502327), p. 9, Lemma 2.2 (Dual sparse reconstruction property, l-infinity version), eq. (2.4)

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry

namespace CandesTao.Decoding
theorem dual_reconstruction_linf {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ)
    (hS : 1 ≤ S) (hSm : 3 * S ≤ m)
    (h : restrictedIsometryConst F S + restrictedOrthogonalityConst F S (2 * S) < 1)
    (T : Finset (Fin m)) (c : Fin m → ℝ) (hT : T.card ≤ S) (hc : SupportedOn c T) :
    ∃ w : Fin p → ℝ, w ∈ columnSpan F ∧ (∀ j ∈ T, dotProduct w (column F j) = c j) ∧
      ∀ j, j ∉ T →
        |dotProduct w (column F j)| ≤
          restrictedOrthogonalityConst F S S /
            ((1 - restrictedIsometryConst F S - restrictedOrthogonalityConst F S (2 * S)) *
              Real.sqrt S) * l2Norm c := by sorry
end CandesTao.Decoding
