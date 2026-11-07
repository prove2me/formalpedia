-- Prove2me | Theorems.Thm_AvgValueAlloc_theorem_1_2
-- name    : AvgValueAlloc.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:41:39.941209+00:00
-- url     : https://prove2.me/theorems/349a97f7-5b89-40ec-8ac0-f8a2c1b3d9f0
-- title:
--   Theorem 1.2 — Fixed-input lower bounds
-- statement:
--   There is an absolute constant $a>0$ such that for every number of buyers $n$, every thresholds $\rho\in\mathbb Q^n_{>0}$, every $T\ge1$, $S\ge0$ and $1\le d\le\kappa(\rho)$:
--
--   1. every causal learner has a finite rational law $D$ of ambiguity exactly $d$ with $\mathrm{OPT}_{\mathrm{on}}(D,T)>0$ and $\mathrm{OPT}_{\mathrm{on}}(D,T)\ge a\,\Phi(d,T,S)\,\mathbb E\,\mathrm{ALG}$;
--   2. some finite rational law $D$ of ambiguity exactly $d$ has $\mathbb E\,\mathrm{OPT}_{\mathrm{off}}(Q)\ge a\,\Psi(d,T)\,\mathrm{OPT}_{\mathrm{on}}(D,T)>0$, even with $D$ revealed;
--   3. every learner has a fixed population $P$ of exactly $S+T$ items, all of whose sponsors are local, with ambiguity $\sigma_P=d$, $\mathrm{OPT}_{\mathrm{inv}}(P;S,T)>0$ and $\mathrm{OPT}_{\mathrm{inv}}(P;S,T)\ge a\,\Psi(d,T)\,\mathbb E\,\mathrm{ALG}$;
--   4. the same population lower bound holds with exactly one sponsor in the entire population.
--
--   All original buyers and thresholds are preserved; learners may use unlimited computation and know the candidate family. These lower bounds make the rows of Table 1 sharp.
--
--   Differences from the source:
--   - generalization: (i) a law with OPT_on(D, T) ≥ aΦ(d, T, S)E ALG → also OPT_on(D, T) > 0; reason: at d = 1 the all-zero law has ambiguity exactly 1 and OPT_on = 0, so (i) as printed holds emptily there; the paper's constructions have a positive benchmark (p.12 bounded cases, p.13 for (iii))
--   - generalization: (iii), (iv) a population with OPT_inv(P; S, T) ≥ aΨ(d, T)E ALG → also OPT_inv(P; S, T) > 0; reason: p.13: "With a smaller absolute constant it can be chosen with positive benchmark"; excludes the empty all-zero population
--   - reading: every causal learner; learners may use unlimited computation and know the candidate family → every CausalLearner (any probability space, measurable decisions from history, past, current item and randomness) satisfying (1) on every outcome, fixed before the law or population; reason: a learner feasible on realized outcomes becomes everywhere feasible, with the same welfare there, by rejecting violating moves; fixing it first lets it depend on the family
--   - reading: (iii) local sponsors → every sponsor of P is local; reason: the local random-order class requires every sponsor to be local (p.2)
--   - reading: (iv) exactly one sponsor in the entire population → exactly one index i with J(P_i) ≠ ∅, and that sponsor local, σ_P = d, OPT_inv > 0; reason: "the preceding population lower also holds": the population of (iii) with the extra restriction; p.13: "Every fixed population has exactly one positive item and retains the original thresholds and ambiguity d"
--   - encoding: ambiguity exactly d; finite rational law → sigmaLaw ρ D = d (resp. σ_P = d); FinLaw with positive rational weights; reason: Lean convention; same instances
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), Theorem 1.2, p.3

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_FinLaw
import Definitions.Def_AvgValueAlloc_iidE
import Definitions.Def_AvgValueAlloc_OPTon
import Definitions.Def_AvgValueAlloc_OPToff
import Definitions.Def_AvgValueAlloc_OPTinv
import Definitions.Def_AvgValueAlloc_kappa
import Definitions.Def_AvgValueAlloc_sigmaOn
import Definitions.Def_AvgValueAlloc_Phi
import Definitions.Def_AvgValueAlloc_posSet
import Definitions.Def_AvgValueAlloc_CausalLearner

namespace AvgValueAlloc

open scoped ENNReal

open scoped Classical in
/-- **Theorem 1.2 (Fixed-input lower bounds).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), Theorem 1.2, p.3: "There is an absolute a > 0 such that for
every prescribed ρ, T, S and 1 ≤ d ≤ κ(ρ): (i) every causal learner has a finite rational law of
ambiguity exactly d with OPT_on(D, T) ≥ aΦ(d, T, S)E ALG; (ii) some such law satisfies E OPT_off(Q)
≥ aΨ(d, T) OPT_on(D, T) > 0, even with D revealed; (iii) every learner has a fixed population of
exactly S + T items with local sponsors and ambiguity d for which OPT_inv(P; S, T) ≥ aΨ(d, T)E ALG;
(iv) the preceding population lower also holds with exactly one sponsor in the entire population.
All original buyers and thresholds are preserved. Learners may use unlimited computation and know
the candidate family."

There is `a > 0` such that for every `n`, thresholds `ρ > 0`, `T ≥ 1`, `S ≥ 0` and
`1 ≤ d ≤ κ(ρ)`:
1. every causal learner satisfying (1) has a finite rational law `D` with `σ(D, ρ) = d`,
   `OPT_on(D, T) > 0` and `OPT_on(D, T) ≥ aΦ(d, T, S) E ALG(D)`;
2. some finite rational law `D` with `σ(D, ρ) = d` has `OPT_on(D, T) > 0` and
   `E_{Q∼D^T} OPT_off(Q) ≥ aΨ(d, T) OPT_on(D, T)`;
3. every such learner has a population `P` of `S + T` items, all of whose sponsors are local, with
   `σ_P = d`, `OPT_inv(P; S, T) > 0` and `OPT_inv(P; S, T) ≥ aΨ(d, T) E ALG(P)`;
4. the same as 3 with exactly one sponsor among the `S + T` items.

**Formalization Note.** Learners are `CausalLearner`s (unlimited computation, any randomness); a
learner is fixed before the law or population, so it may know the whole candidate family. The
positivity clauses in 1, 3 and 4 exclude laws or populations with zero benchmark. -/
theorem theorem_1_2 :
    ∃ a : ℝ, 0 < a ∧ ∀ (n : ℕ) (ρ : Fin n → ℚ), (∀ j, 0 < ρ j) → ∀ T S d : ℕ, 1 ≤ T → 1 ≤ d →
      d ≤ kappa ρ →
      (∀ L : CausalLearner n S T, L.Feasible ρ →
        ∃ D : FinLaw n, D.IsLaw ∧ D.IsRational ∧ sigmaLaw ρ D = d ∧ 0 < OPTon ρ D T ∧
          ENNReal.ofReal (a * Phi d T S) * L.EALGiid D ≤ OPTon ρ D T) ∧
      (∃ D : FinLaw n, D.IsLaw ∧ D.IsRational ∧ sigmaLaw ρ D = d ∧ 0 < OPTon ρ D T ∧
        ENNReal.ofReal (a * Psi d T) * OPTon ρ D T ≤ iidE D (Fin T) (OPToff ρ)) ∧
      (∀ L : CausalLearner n S T, L.Feasible ρ →
        ∃ P : Fin (S + T) → Vec n, AllSponsorsLocal ρ P ∧
          sigmaOn ρ (Finset.univ.image P) = d ∧ 0 < OPTinv ρ S T P ∧
          ENNReal.ofReal (a * Psi d T) * L.EALGpop P ≤ OPTinv ρ S T P) ∧
      (∀ L : CausalLearner n S T, L.Feasible ρ →
        ∃ P : Fin (S + T) → Vec n,
          (Finset.univ.filter fun i => IsSponsor ρ (P i)).card = 1 ∧ AllSponsorsLocal ρ P ∧
          sigmaOn ρ (Finset.univ.image P) = d ∧ 0 < OPTinv ρ S T P ∧
          ENNReal.ofReal (a * Psi d T) * L.EALGpop P ≤ OPTinv ρ S T P) := by sorry

end AvgValueAlloc
