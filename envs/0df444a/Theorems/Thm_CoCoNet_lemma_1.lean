-- Prove2me | Theorems.Thm_CoCoNet_lemma_1
-- name    : CoCoNet.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:05.258276+00:00
-- url     : https://prove2.me/theorems/a5aa3e7c-f410-4b7a-977b-02a1960786eb
-- title:
--   Lemma 1 — every price vector is an equilibrium for a unique partition and asset vector
-- statement:
--   Let $(m,W)$ be an admissible network, $l\ge 0$ the thresholds and $c$ the credit amounts. For every $s\in\mathbb R^n$:
--   1. there is exactly one partition $(B,C,H)$ of $[n]$ for which some asset vector $a$ makes $(a,s)$ a $(B,C,H)$-equilibrium;
--   2. $(a,s)$ is a $(B,C,H)$-equilibrium if and only if
--   $$B=\{i:s_i<0\},\quad C=\{i:0\le s_i\le l_i\},\quad H=\{i:s_i>l_i\},\quad a=\Phi(s),$$
--   where $\Phi(s)$ is the unique solution of the linear system (1)–(2) for this partition.
--
--   So the map $\Phi$ from stock prices to asset values is well defined, and the equilibrium question becomes whether $\Phi$ is onto (existence) or one-to-one (uniqueness).
--
--   Differences from the source:
--   - reading: no sign condition on the thresholds l stated → 0 ≤ l; reason: the paper asserts that the sets S_{B,C,H} partition ℝⁿ (p.12), which holds iff l ≥ 0; in the paper's setting lᵢ ≥ cᵢ/mᵢ with nonnegative debts cᵢ; without it the sets read off s overlap and Φ is not continuous
--   - generalization: credit amounts cᵢ are convertible debts (implicitly cᵢ ≥ 0) → c : Fin n → ℝ of any sign; reason: equations (1)–(2) and (3) are linear in c and the proof never uses c ≥ 0; nonnegative c is a special case
--   - encoding: a is the unique solution of the linear system (1–2) for the partition read off s → a = Phi m W l c s, the formula (3); reason: (3) is the paper's summary of (1)–(2) (p.11)
--   - encoding: banks [n] = {1, …, n}; vectors in ℝⁿ; matrix W = (w_ij) → banks Fin n (0-based); vectors Fin n → ℝ; W : Matrix (Fin n) (Fin n) ℝ with W i j = w_ij; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, Lemma 1, p.10

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_bankrupt
import Definitions.Def_CoCoNet_converting
import Definitions.Def_CoCoNet_healthy
import Definitions.Def_CoCoNet_IsEquilibrium
import Definitions.Def_CoCoNet_Phi

namespace CoCoNet

/-- **Lemma 1 (every price vector is an equilibrium for exactly one partition and one asset
vector).**
Balter, Schweizer & Vera, arXiv:2011.06474v1, Lemma 1, p.10: "For every s ∈ ℝⁿ, there exist a
unique partition (B, C, H) of [n] and an asset price vector a such that (a, s) is a
(B, C, H)-equilibrium. Specifically, the partition (B, C, H) is given by B = {i|sᵢ < 0},
C = {i|0 ≤ sᵢ ≤ lᵢ} and H = {i|sᵢ > lᵢ} and the asset price vector is given by the unique
solution a to the linear system (1–2) for this partition (B, C, H)."

The first conjunct is the existence and uniqueness of the partition; the second says that
`(a, s)` is a `(B, C, H)`-equilibrium exactly when `(B, C, H)` is the partition read off `s` and
`a = Φ(s)`, the unique solution of (1–2).

**Formalization Note.** `0 ≤ l` is a reading: it is what makes the three sets read off `s` a
partition of `[n]` (p.12). -/
theorem lemma_1 {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l c : Fin n → ℝ)
    (hadm : IsAdmissible m W) (hl : 0 ≤ l) (s : Fin n → ℝ) :
    (∃! P : Finset (Fin n) × Finset (Fin n) × Finset (Fin n),
        ∃ a : Fin n → ℝ, IsEquilibrium m W l c a s P.1 P.2.1 P.2.2) ∧
    ∀ (a : Fin n → ℝ) (B C H : Finset (Fin n)),
      IsEquilibrium m W l c a s B C H ↔
        (B = bankrupt s ∧ C = converting l s ∧ H = healthy l s ∧ a = Phi m W l c s) := by sorry

end CoCoNet
