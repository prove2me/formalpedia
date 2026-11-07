-- Prove2me | Theorems.Thm_AvgValueAlloc_theorem_1_1
-- name    : AvgValueAlloc.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:42:10.869696+00:00
-- url     : https://prove2.me/theorems/25062666-5bd8-41b8-aa94-b5f2d1b7dcc3
-- title:
--   Theorem 1.1 — one polynomial-time learner attains Table 1
-- statement:
--   There are one randomized polynomial-time learner and absolute constants $C,a>0$ with the following properties, for every number of buyers $n$, thresholds $\rho\in\mathbb Q^n_{>0}$, horizon $T\ge1$ and history length $S\ge0$. The learner sees only $\rho$, $T$, $S$, the history and the live stream; it knows neither the arrival model nor the ambiguity, the support or the locality promise.
--
--   1. **Feasibility.** Its decisions satisfy (1) on every outcome: every history, live sequence and coin tape.
--   2. **i.i.d. information.** For every finite law $D$: $\ \mathrm{OPT}_{\mathrm{on}}(D,T)\le C\,\Phi(\sigma(D,\rho),T,S)\,\mathbb E\,\mathrm{ALG}$.
--   3. **i.i.d. foresight.** For every finite law $D$: $\ \mathbb E_{Q\sim D^T}\mathrm{OPT}_{\mathrm{off}}(Q)\le C\,\Psi(\sigma(D,\rho),T)\,\mathbb E\,\mathrm{ALG}$.
--   4. **Random order.** For every population $P$ of $S+T$ items in uniform order (first $S$ history, last $T$ live): $\ \mathbb E\,\mathrm{OPT}_{\mathrm{off}}(\text{live})\le C\,\Lambda(\sigma_P,T)\,\mathbb E\,\mathrm{ALG}$, and $\mathrm{OPT}_{\mathrm{inv}}(P;S,T)\le\mathbb E\,\mathrm{OPT}_{\mathrm{off}}(\text{live})$.
--   5. **All-local random order.** If every sponsor of $P$ is local: $\ \mathbb E\,\mathrm{OPT}_{\mathrm{off}}(\text{live})\le C\,\Psi(\sigma_P,T)\,\mathbb E\,\mathrm{ALG}$.
--   6. **Sharpness.** For every $1\le d\le\kappa(\rho)$ the lower bounds (i)–(iii) of Theorem 1.2 hold with the constant $a$.
--
--   No probability floor, support, value or spread bound, initial bank or minimum funding rate is assumed. The rates are $\Theta(\Phi)$, $\Theta(\Psi)$, $O(\Lambda)$ and $\Theta(\Psi)$, as in Table 1.
--
--   **Formalization Note** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime`; the learner's map, its coin polynomial and the constants are chosen before $n,\rho,T,S$ and the law or population.
--
--   Differences from the source:
--   - reading: one randomized polynomial-time learner; runtime polynomial in n, S, T and observed binary input → a map alg with Turing.TM2ComputableInPolyTime encIn encNat alg and a polynomial p, fixed before n, ρ, T, S; each decision is alg on the observation (binary rationals, T and S in unary) and the first p(|observation|) bits of one fair coin tape; output 0 or out of range rejects, k + 1 assigns buyer k; reason: Mathlib's Turing-machine model; unary T, S put n, S, T into the input length; nested coin prefixes model one physical execution with fresh fair bits (Appendix A.2)
--   - generalization: Table 1 rates on σ ≤ d classes → rates at the exact ambiguity σ(D, ρ), σ_P; reason: Φ, Ψ, Λ are nondecreasing in d, so the bound at σ gives the bound on every class σ ≤ d; the learner adapts (abstract, p.1)
--   - encoding: random order on an unknown fixed live multiset Q, or an exact population with history → a population P of S + T items in uniform order, the first S history, the last T live; S = 0 is the fixed live multiset; E_π OPT_off(live) as the final-offline benchmark; reason: §4, p.10: "Average the conditional final-offline bound"; at S = 0, OPT_off(live) = OPT_off(Q) and σ_P = σ_Q
--   - encoding: OPT_off(Q); hence population-known causal → E_π OPT_off(live) ≤ CΛ E ALG and OPT_inv(P; S, T) ≤ E_π OPT_off(live); reason: the "hence" clause stated as the comparison the paper uses (§4, p.10: "use OPT_inv(P; S, T) ≤ E_history OPT_off(Q)")
--   - encoding: Θ in rows 1, 2, 4 (minimax, sharp) → the upper bounds for the learner and, with the same absolute a, clauses (i)–(iii) of Theorem 1.2 for every 1 ≤ d ≤ κ(ρ); reason: the lower halves of the Θ rows are Theorem 1.2 (§4, p.10 cites Theorem 1.2(iii) for the local row); row 3 is O only, as the caption says
--   - generalization: Theorem 1.2 (i), (iii) as lower halves → with OPT_on(D, T) > 0 and OPT_inv(P; S, T) > 0 added; reason: as in Theorem 1.2: excludes the all-zero law and population, for which (i) and (iii) hold emptily
--   - reading: learners of the lower bounds → CausalLearner satisfying (1) on every outcome; reason: as in Theorem 1.2
--   - encoding: benchmarks and expectations → values in ℝ≥0∞, constants cast by ENNReal.ofReal; reason: no junk supremum; same instances
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), Theorem 1.1 and Table 1, p.3

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_FinLaw
import Definitions.Def_AvgValueAlloc_iidE
import Definitions.Def_AvgValueAlloc_prefixFeasible
import Definitions.Def_AvgValueAlloc_OPTon
import Definitions.Def_AvgValueAlloc_OPToff
import Definitions.Def_AvgValueAlloc_popAvg
import Definitions.Def_AvgValueAlloc_OPTinv
import Definitions.Def_AvgValueAlloc_kappa
import Definitions.Def_AvgValueAlloc_sigmaOn
import Definitions.Def_AvgValueAlloc_Phi
import Definitions.Def_AvgValueAlloc_posSet
import Definitions.Def_AvgValueAlloc_LearnerInput
import Definitions.Def_AvgValueAlloc_encIn
import Definitions.Def_AvgValueAlloc_tapeDec
import Definitions.Def_AvgValueAlloc_coinTape
import Definitions.Def_AvgValueAlloc_expIID
import Definitions.Def_AvgValueAlloc_CausalLearner

namespace AvgValueAlloc

open scoped ENNReal

/-- **Theorem 1.1 with Table 1 (one polynomial-time learner, sharp rates).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), Theorem 1.1, p.3: "One randomized polynomial-time learner
satisfies (1) on every outcome and simultaneously attains Table 1, with absolute implicit constants.
It needs no knowledge of the arrival model, ambiguity or support. No probability floor,
support/value/spread bound, initial bank or minimum funding rate is assumed." Table 1, p.3: i.i.d.
with S independent history against OPT_on(D, T): Θ(Φ(d, T, S)); i.i.d., any S, against
E OPT_off(Q): Θ(Ψ(d, T)); random order against OPT_off(Q), hence population-known causal: O(Λ(d, T));
random order, all sponsors local, same benchmarks: Θ(Ψ(d, T)). Caption: "Minimax i.i.d. rates on
σ ≤ d classes at each prescribed ρ. For random order use σ_Q ≤ d, or σ_P ≤ d for an exact population
with history. Its lower is Ω(Ψ), not a matching Ω(Λ) claim. The local row is sharp on the all-local
σ ≤ d class at each prescribed threshold vector; the learner is not given the locality promise."

There are a deterministic map `alg` computable by a Turing machine in polynomial time, a polynomial
`p` and absolute constants `C, a > 0` such that, for every `n`, thresholds `ρ > 0`, `T ≥ 1` and
`S ≥ 0`, the learner `L` that decides each live item by `alg` on its observation and the first
`p(|observation|)` bits of a fair coin tape satisfies:
1. (1) holds for every history, live sequence and coin tape;
2. `OPT_on(D, T) ≤ C Φ(σ(D, ρ), T, S) E ALG` for every finite law `D`;
3. `E_{Q∼D^T} OPT_off(Q) ≤ C Ψ(σ(D, ρ), T) E ALG` for every finite law `D`;
4. for every population `P` of `S + T` items in uniform order (first `S` history, last `T`
   live): `E OPT_off(live) ≤ C Λ(σ_P, T) E ALG`, and `OPT_inv(P; S, T) ≤ E OPT_off(live)`;
5. for every such `P` all of whose sponsors are local: `E OPT_off(live) ≤ C Ψ(σ_P, T) E ALG`;
6. for every `1 ≤ d ≤ κ(ρ)`, the lower bounds (i)–(iii) of Theorem 1.2 hold with this `a`.

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` over
`encIn`/`OnlineCRS.Combine.encNat` (binary rationals, `T` and `S` in unary); output `0` or an
out-of-range code rejects, `k + 1` assigns buyer `k`. `alg`, `p`, `C`, `a` are fixed before
`n`, `ρ`, `T`, `S` and the law or population, so the learner knows no arrival model, ambiguity,
support or locality. The rates are stated at the exact ambiguity `σ`, which gives the `σ ≤ d`
classes because `Φ, Ψ, Λ` are nondecreasing in `d`. -/
theorem theorem_1_1 :
    ∃ (alg : LearnerInput × List Bool → ℕ) (p : Polynomial ℕ) (C a : ℝ), 0 < C ∧ 0 < a ∧
      Nonempty (Turing.TM2ComputableInPolyTime encIn OnlineCRS.Combine.encNat alg) ∧
      ∀ (n : ℕ) (ρ : Fin n → ℚ), (∀ j, 0 < ρ j) → ∀ T S : ℕ, 1 ≤ T →
        (∀ (hist : Fin S → Vec n) (vs : Fin T → Vec n) (ω : ℕ → Bool),
          prefixFeasible ρ vs (tapeDec alg p ρ T S hist vs ω)) ∧
        (∀ D : FinLaw n, D.IsLaw →
          OPTon ρ D T ≤ ENNReal.ofReal (C * Phi (sigmaLaw ρ D) T S) *
            expIID D S T coinTape (tapeDec alg p ρ T S)) ∧
        (∀ D : FinLaw n, D.IsLaw →
          iidE D (Fin T) (OPToff ρ) ≤ ENNReal.ofReal (C * Psi (sigmaLaw ρ D) T) *
            expIID D S T coinTape (tapeDec alg p ρ T S)) ∧
        (∀ P : Fin (S + T) → Vec n,
          popAvg S T (fun _ Q => OPToff ρ Q) P ≤
              ENNReal.ofReal (C * Lam (sigmaOn ρ (Finset.univ.image P)) T) *
                expPop S T P coinTape (tapeDec alg p ρ T S) ∧
            OPTinv ρ S T P ≤ popAvg S T (fun _ Q => OPToff ρ Q) P) ∧
        (∀ P : Fin (S + T) → Vec n, AllSponsorsLocal ρ P →
          popAvg S T (fun _ Q => OPToff ρ Q) P ≤
            ENNReal.ofReal (C * Psi (sigmaOn ρ (Finset.univ.image P)) T) *
              expPop S T P coinTape (tapeDec alg p ρ T S)) ∧
        (∀ d : ℕ, 1 ≤ d → d ≤ kappa ρ →
          (∀ L : CausalLearner n S T, L.Feasible ρ →
            ∃ D : FinLaw n, D.IsLaw ∧ D.IsRational ∧ sigmaLaw ρ D = d ∧ 0 < OPTon ρ D T ∧
              ENNReal.ofReal (a * Phi d T S) * L.EALGiid D ≤ OPTon ρ D T) ∧
          (∃ D : FinLaw n, D.IsLaw ∧ D.IsRational ∧ sigmaLaw ρ D = d ∧ 0 < OPTon ρ D T ∧
            ENNReal.ofReal (a * Psi d T) * OPTon ρ D T ≤ iidE D (Fin T) (OPToff ρ)) ∧
          (∀ L : CausalLearner n S T, L.Feasible ρ →
            ∃ P : Fin (S + T) → Vec n, AllSponsorsLocal ρ P ∧
              sigmaOn ρ (Finset.univ.image P) = d ∧ 0 < OPTinv ρ S T P ∧
              ENNReal.ofReal (a * Psi d T) * L.EALGpop P ≤ OPTinv ρ S T P)) := by sorry

end AvgValueAlloc
