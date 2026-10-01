-- Prove2me | Theorems.Thm_CandesTao_Decoding_dual_reconstruction_l2
-- name    : CandesTao.Decoding.dual_reconstruction_l2
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-30T22:16:42.247202+00:00
-- url     : https://prove2.me/theorems/cb43db03-1b63-49de-9bcf-abb07e2a855e
-- title:
--   Lemma 2.1: dual sparse reconstruction property, $\ell^2$ version
-- statement:
--   Let $F$ be a real $p \times m$ matrix with columns $v_1, \dots, v_m$ spanning $H$. Let $S, S' \ge 1$ be such that $\delta_S < 1$, and let $c$ be a real vector supported on $T \subseteq \{1, \dots, m\}$ with $|T| \le S$. Then there exists a vector $w \in H$ such that
--   $$
--   \langle w, v_j \rangle = c_j \quad \text{for all } j \in T .
--   $$
--   Furthermore, there is an *exceptional set* $E \subseteq \{1, \dots, m\}$, disjoint from $T$, of size $|E| \le S'$, with the properties
--   $$
--   |\langle w, v_j \rangle| \le \frac{\theta_{S,S'}}{(1 - \delta_S)\sqrt{S'}} \, \|c\| \quad \text{for all } j \notin T \cup E
--   \qquad \text{and} \qquad
--   \Big( \sum_{j \in E} |\langle w, v_j \rangle|^2 \Big)^{1/2} \le \frac{\theta_{S,S'}}{1 - \delta_S} \, \|c\| .
--   $$
--   In addition, $\|w\| \le K \, \|c\|$ for some constant $K > 0$ depending only on $\delta_S$.
--
--   This is the first half of the dual certificate construction: a vector $w$ that interpolates prescribed values on $T$ and whose inner products with the columns outside $T$ are small in an $\ell^2$ sense, uniformly small outside an exceptional set of controlled size. Lemma 2.2 iterates it to remove the exceptional set.
--
--   **Formalization Note** The paper prints the second bound with $\theta_S = \theta_{S,S}$; the inequality (2.3) established in its proof, and the use of the lemma in Lemma 2.2 with $S' = S$, give $\theta_{S,S'}$, which is what is stated here (the two agree when $S' = S$). "A constant $K > 0$ depending only on $\delta_S$" is formalized as a positive function $K$ of the real number $\delta_S$, chosen before $F$, $S$, $S'$, $T$ and $c$. The hypothesis $S + S' \le m$ is the domain on which Definition 1.1 defines $\theta_{S,S'}$.
-- source:
--   Candès--Tao 2005, Decoding by Linear Programming, IEEE Trans. Inform. Theory 51(12):4203-4215, doi:10.1109/TIT.2005.858979; arXiv:math/0502327v1 (https://arxiv.org/abs/math/0502327), p. 8, Lemma 2.1 (Dual sparse reconstruction property, l2 version), with eqs. (2.1)-(2.3) of its proof, pp. 8-9

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry

namespace CandesTao.Decoding
theorem dual_reconstruction_l2 :
    ∃ K : ℝ → ℝ, (∀ δ : ℝ, 0 < K δ) ∧
    ∀ {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S S' : ℕ),
      1 ≤ S → 1 ≤ S' → S + S' ≤ m → restrictedIsometryConst F S < 1 →
      ∀ (T : Finset (Fin m)) (c : Fin m → ℝ), T.card ≤ S → SupportedOn c T →
      ∃ w : Fin p → ℝ, w ∈ columnSpan F ∧
        (∀ j ∈ T, dotProduct w (column F j) = c j) ∧
        (∃ E : Finset (Fin m), Disjoint E T ∧ E.card ≤ S' ∧
          (∀ j, j ∉ T → j ∉ E →
            |dotProduct w (column F j)| ≤
              restrictedOrthogonalityConst F S S' /
                ((1 - restrictedIsometryConst F S) * Real.sqrt S') * l2Norm c) ∧
          Real.sqrt (∑ j ∈ E, dotProduct w (column F j) ^ 2) ≤
            restrictedOrthogonalityConst F S S' / (1 - restrictedIsometryConst F S) * l2Norm c) ∧
        l2Norm w ≤ K (restrictedIsometryConst F S) * l2Norm c := by sorry
end CandesTao.Decoding
