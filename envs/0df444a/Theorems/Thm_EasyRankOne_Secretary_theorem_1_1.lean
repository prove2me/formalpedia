-- Prove2me | Theorems.Thm_EasyRankOne_Secretary_theorem_1_1
-- name    : EasyRankOne.Secretary.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:06:33.850438+00:00
-- url     : https://prove2.me/theorems/fe134b18-c999-457c-b658-7c9b1d29ea45
-- title:
--   Theorem 1.1 (formal version Theorem 6.1) — an ordinal matroid secretary program knowing only n accepts each optimum element independently with probability 1/e, in expected polynomial time and queries
-- statement:
--   There are one program $P$ of the online oracle machine and universal constants $C>0$, $k\in\mathbb N$, fixed before the instance, such that the following holds for every finite ground set $V$ with a label order, $n=|V|$, every matroid $M$ on $V$ and every nonnegative values $v:V\to\mathbb R$. The elements of $V$ arrive in a uniformly random order $\pi$, independent of $P$'s uniform tape $\omega$; $P$ receives only $n$, refers to elements by arrival index, sees values only through tie-broken comparisons of arrived elements (ordinal), and queries independence only of sets of arrived elements.
--   1. **Feasibility.** On every run (every order, every tape in $(0,1)^{\mathbb N}$) $P$ executes no invalid instruction — no repeated decision or next arrival before the current decision, and comparisons and queries only on arrived elements; almost-sure halting below ensures all arrivals are decided almost surely — and its accepted set $\mathrm{ALG}$ is independent in $M$.
--   2. **Optimal guarantee.** The elements of the canonical optimum $\mathrm{Greedy}(V)$ are accepted independently, each with probability exactly $1/e$:
--   $$\Pr[S\subseteq\mathrm{ALG}]=e^{-|S|}\qquad\text{for every } S\subseteq \mathrm{Greedy}(V).$$
--   3. **Efficiency.** The run halts with probability $1$, and the expected number of executed instructions (arithmetic, comparisons, $\ln$, $\exp$, uniform draws) and the expected number of independence queries are each at most $C n^k+C$; expectations and probabilities are over the uniform arrival order and the tape.
--
--   This resolves the strong matroid secretary conjecture: ratio $e$, matching rank one, with per-element (probability-competitive) guarantees.
--
--   Differences from the source:
--   - reading: "there is an ordinal secretary algorithm … knowing only n … uses an expected polynomial number of independence queries on subsets of arrived elements" → one program of the online oracle machine (published SmaleNinth real-RAM core with integer memory, ln, exp, a uniform tape and the instructions arrive/cmp/indep/accept/reject/halt on arrival indices), given only n in memory; reason: the paper names only "the randomized real RAM" (p. 22) and the secretary model (p. 6)
--   - reading: Theorem 1.1's query bound → also Theorem 6.1's expected arithmetic bound (executed instructions), with "polynomial" read as ≤ C·n^k + C, C > 0 and k universal and quantified before the instance, plus halting with probability 1; reason: Theorem 6.1 is the formal version of Theorem 1.1
--   - reading: "accepts the elements of the canonical optimum independently, each with probability 1/e" → Pr[S ⊆ ALG] = e^{−|S|} for every finite S ⊆ Greedy(V); reason: mutual independence with marginals 1/e
--   - reading: the model's "must irrevocably accept or reject it before the next arrival; the accepted set must be independent; independence queries may involve only observed elements" → asserted on every run with a tape in (0,1)^ℕ, not assumed; reason: these are requirements on the algorithm, part of what is claimed
--   - encoding: uniformly random order, independent of the algorithm's randomness → probability averaged over the n! bijections Fin n ≃ V of the measure of the i.i.d. Uniform(0,1) tape; expectations as lower integrals in [0, ∞] with ∞ for a non-halting run; a fixed order of labels → the `LinearOrder` of a finite type `α : Type`, `M.E = univ`; reason: Lean convention, same instances
--   - generalization: a program of the randomized real RAM → an `Admissible` program: rational literals only, the core's accept/reject unused; reason: every admissible program is a real-RAM program, so the existence claimed specializes to the source's
-- source:
--   Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, As Easy as Rank One, STOC 2027 submission (manuscript of November 2026, sha256 f74f3f91…), p. 1, Theorem 1.1 and footnote 1; formal version p. 23, Theorem 6.1; models p. 6 (§2.2) and p. 22 (§6)

import Mathlib
import Definitions.Def_EasyRankOne_Secretary_Greedy
import Definitions.Def_EasyRankOne_Secretary_Machine

open MeasureTheory
open scoped ENNReal

namespace EasyRankOne.Secretary

theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ P : Program, Admissible P ∧
      ∀ (α : Type) [Fintype α] [LinearOrder α] (M : Matroid α), M.E = Set.univ →
      ∀ v : α → ℝ, (∀ a, 0 ≤ v a) →
        (∀ (π : Fin (Fintype.card α) ≃ α) (ω : ℕ → ℝ), TapeInSupport ω →
            RunValid M v π P ω ∧ M.Indep (ALG M v π P ω)) ∧
        (∀ S : Finset α, (↑S : Set α) ⊆ Greedy M v Set.univ →
            runProb (fun π ω => (↑S : Set α) ⊆ ALG M v π P ω) = Real.exp (-(S.card : ℝ))) ∧
        runProb (fun π ω => RunHalts M v π P ω) = 1 ∧
        runExp (fun π ω => totalWork M v π P ω) ≤
          ENNReal.ofReal (C * (Fintype.card α : ℝ) ^ k + C) ∧
        runExp (fun π ω => totalQueries M v π P ω) ≤
          ENNReal.ofReal (C * (Fintype.card α : ℝ) ^ k + C) := by sorry

end EasyRankOne.Secretary
