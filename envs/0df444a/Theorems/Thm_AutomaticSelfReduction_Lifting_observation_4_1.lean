-- Prove2me | Theorems.Thm_AutomaticSelfReduction_Lifting_observation_4_1
-- name    : AutomaticSelfReduction.Lifting.observation_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:55.480486+00:00
-- url     : https://prove2.me/theorems/a382b497-76b2-4cc1-931f-569e3bb7578d
-- title:
--   Observation 4.1 — round elimination of a 2-separated problem is the side-swapped problem up to renaming
-- statement:
--   Let $\Pi=(\Sigma,\Delta,\delta,C_W,C_B)$ be a normalized 2-separated problem and $\Pi'=R(\Pi)$. Then, up to renaming of labels,
--   $$
--   \Pi'=(\Sigma,\delta,\Delta,C_B,C_W).
--   $$
--   That is, there is a bijection between the label set $\Sigma'$ of $R(\Pi)$ and $\Sigma$ that carries the active constraint $C'_B$ of $R(\Pi)$ exactly onto $C_B$ and its passive constraint $C'_W$ exactly onto $C_W$.
--
--   Applied twice, the observation gives $R(R(\Pi))=\Pi$ up to renaming, which is what lets the speedup of Lemma 5.2 be iterated on a single problem.
--
--   **Formalization Note** The conclusion is `Nonempty (Problem.Equiv (R P) P.swap)`, where `P.swap` is $(\Sigma,\delta,\Delta,C_B,C_W)$ and `Problem.Equiv` is a bijection of label types under which membership in each constraint is preserved in both directions.
--
--   Differences from the source:
--   - encoding: up to renaming of labels, Π' = (Σ, δ, Δ, C_B, C_W) → a bijection RLabel P ≃ L carrying (R P).CW onto C_B and (R P).CB onto C_W; reason: this is the meaning of equality up to renaming; the labels of R P are the subtype Σ' of Finset L
--   - generalization: Σ a finite set of labels (Definition 2.4) → an arbitrary label type L, no finiteness assumed; reason: the argument uses only 2-separation and normalization; a finite Σ is an instance
-- source:
--   Alkida Balliu, Francesco d’Amore, Dennis Olivetti, Distributed Lower Bounds via Automatic Self-Reduction, STOC 2027 submission #338 (October 2026), Observation 4.1, printed p. 11 (PDF p. 12); normalization assumption after Definition 2.4, printed p. 6 (PDF p. 7)

import Definitions.Def_AutomaticSelfReduction_Lifting_Problem

namespace AutomaticSelfReduction.Lifting

/-- Observation 4.1 (Balliu–d'Amore–Olivetti, STOC 2027 submission #338, PDF p. 12, printed
p. 11). Let `Π = (Σ, Δ, δ, C_W, C_B)` be a 2-separated problem (normalized, as assumed throughout
the paper) and `Π' = R(Π)`. Then, up to renaming of labels, `Π' = (Σ, δ, Δ, C_B, C_W)`. -/
theorem observation_4_1 {L : Type*} [DecidableEq L] {Δ δ : ℕ} (P : Problem L Δ δ)
    (hN : P.IsNormalized) (h2 : P.TwoSeparated) :
    Nonempty (Problem.Equiv (R P) P.swap) := by sorry

end AutomaticSelfReduction.Lifting
