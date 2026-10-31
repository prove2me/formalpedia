-- Prove2me | Theorems.Thm_FirstChoiceDesign_theorem_1
-- name    : FirstChoiceDesign.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:13.12463+00:00
-- url     : https://prove2.me/theorems/d1042df7-bdcb-42b4-bd21-08686afc16bb
-- title:
--   Theorem 1, p.14 — strategy-proofness for schools implies the first-choice design extracts a random assignment
-- statement:
--   **Theorem 1.** The first-choice research design extracts a random assignment for a gDA mechanism $\varphi$ if $\varphi$ is strategy-proof for schools. That is, if $\varphi$ is strategy-proof for schools, then for any assignment problem $X$, any school $s$, any potential lottery realization $r$ and any students $j,k\in\mathit{First}_s(r)$,
--
--   $$
--   P(D_{js}(R)=1)=P(D_{ks}(R)=1).
--   $$
--
--   The theorem justifies comparing assigned and unassigned first-choice applicants as a natural experiment for the Boston mechanism and any other strategy-proof gDA mechanism: strategy-proofness is used as a mathematical property of the algorithm, with no behavioural claim about schools.
--
--   **Formalization Note** The statement is for every gDA mechanism, with either lottery regime, every admissible $f^\varphi$, $g^\varphi$ and every number of priority statuses.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - generalization: reports (ρ_s, r_s) ∈ Γ: ρ_is + r_is ≠ ρ_js + r_js, r ∈ [0,1] (p.13) → ValidReport: numbers in the open interval (0,1), distinct at the school; reason: a subset of Γ, so strategy-proofness in Lean is implied by the source’s and the theorem assumes less; reports in Γ with equal lottery numbers leave Definition 1’s order non-strict and φ undefined
--   - encoding: a preference ≻_s over subsets of I with its weak preference ⪰_s (p.14) → a strict total order pref, with WeakPref := pref ∨ =; reason: a preference is read as a strict total order; a hypothesis over fewer preferences is implied by one over more, and clause (2)–(3) orders are of this kind
--   - reading: R_is independent across schools for each student and iid at each school (pp.6–7) → under MTB all R_is mutually independent (Measure.pi); reason: footnote 7 and "an independent lottery number at each school"
--   - encoding: probabilities P(D_js(R) = 1) → values of lotteryLaw on sets of profiles, in ℝ≥0∞; reason: the law of R; tied profiles form a null set
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Theorem 1, p.14

import Definitions.Def_FirstChoiceDesign_ExtractsRandomAssignment
import Definitions.Def_FirstChoiceDesign_StrategyProofForSchools

namespace FirstChoiceDesign

/-- Theorem 1, Cowles Foundation DP No. 2056R, p.14. The first-choice research design extracts a random assignment
for a gDA mechanism `φ` if `φ` is strategy-proof for schools.

**Formalization Note** `φ` is arbitrary: either lottery regime, any admissible `f`, `g`, any `K`.
Strategy-proofness quantifies over all markets of every size, as Definition 3 does. -/
theorem theorem_1 (φ : GDA) (hφ : StrategyProofForSchools φ) : ExtractsRandomAssignment φ := by sorry

end FirstChoiceDesign
