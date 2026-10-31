-- Prove2me | Theorems.Thm_DworczakDACC_theorem_1
-- name    : DworczakDACC.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:56:04.878851+00:00
-- url     : https://prove2.me/theorems/3ecbcce8-c9a7-4eb2-aa25-9dde8b882393
-- title:
--   Theorem 1 — a matching is stable iff it is the outcome of a DACC algorithm (corrected: stack exit when no acceptable partner remains)
-- statement:
--   Let a one-to-one marriage market have finitely many men and women, at least one agent, and strict preferences of every agent over the other side and the outside option $\emptyset$. Run DACC($\Phi$), the two-sided deferred acceptance algorithm with compensation chains, along an order $\Phi$ that names every agent infinitely often.
--
--   1. For every such $\Phi$ and every order of blocks (a)/(b), DACC($\Phi$) stops in finite time and its outcome is a stable matching.
--   2. Conversely, for every stable matching $\mu$ there is such a $\Phi$ for which $\mu$ is the outcome of DACC($\Phi$), whatever the order of blocks (a)/(b).
--   3. Therefore a matching is stable if and only if it is the outcome of DACC($\Phi$) for some such $\Phi$:
--
--   $$\mu\ \text{stable}\iff \exists\,\Phi,\ \operatorname{ord}:\ \mu=\text{outcome of DACC}(\Phi).$$
--
--   The theorem says that the family of DACC algorithms generalizes one-sided deferred acceptance to proposals from both sides in any order without losing convergence, and that this family reaches every stable matching, not only the two extreme ones.
--
--   Differences from the source:
--   - correction: Algorithm 1, step 4(b)iii (p. 8): remove i from CC if µ(i) ≠ ∅ or Bᵢ = ∅ → remove i from CC if µ(i) ≠ ∅ or argmax{Bᵢ ∪ {∅}; ≻ⁱ} = ∅ (no acceptable partner left in Bᵢ); reason: budgets start full and unacceptable partners never leave them, so a compensated agent with no acceptable partner left applies to ∅ forever under the printed test; in the market m1: w2; m2: w2 ≻ w1; m3: w3 ≻ w1; w1: m2 ≻ m3 ≻ m1; w2: m3 ≻ m1 ≻ m2; w3: nobody, with Φ = m2, w1, m1, w1, (m1, m2, m3, w1, w2, w3) repeated, m3 is stuck on CC from round 6 on and DACC never stops; the corrected test is the paper's own footnote 7 convention and coincides with the printed one when every partner is acceptable; with the printed test the first sentence of the theorem is false
--   - encoding: men M, women W, strict preferences ≻ⁱ on Nᵢ ∪ {∅}, matching and stability as on p. 5 → RuralHospitals.Market D H with capacity h = 1 for all h (men = D, women = H, injective ranks with smaller = better, none = ∅); Market.IsStable; reason: with capacity 1, IsStable is exactly p. 5's stability (one-to-one, acceptable partners, j ≻ⁱ µ(i) ⇒ µ(j) ≻ʲ i); same instances
--   - encoding: any finite market → [Nonempty (D ⊕ H)]; reason: if N = ∅ there is no sequence Φ : ℕ → N, so DACC(Φ) is undefined; the hypothesis excludes only that case
--   - generalization: items (a) and (b) of "i applies" executed in some order (footnote a, p. 8: "in any order, even random") → the order is a parameter ord : ℕ → Bool (one choice per time step), universally quantified; reason: every resolution of footnote a, including a random one along each sample path, is some ord
--   - encoding: DACC(Φ) stops in finite time and its outcome µ → ∃ t with the stopping criterion at run t and µ = the matching of run t (IsOutcome); reason: the run is frozen after it stops, so the outcome is the same at every stopped time
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Theorem 1, p. 7

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_IsAdmissible
import Definitions.Def_DworczakDACC_IsOutcome

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **Theorem 1: every DACC algorithm stops at a stable matching, and every stable matching is
the outcome of some DACC algorithm (stack exit corrected).**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), Theorem 1,
p. 7: "For any sequence Φ, DACC(Φ) stops in finite time and its outcome µ is stable. Conversely,
for an arbitrary stable matching µ, there exists a sequence Φ such that µ is the outcome of
DACC(Φ). Therefore, a matching is stable if and only if it is the outcome of a DACC algorithm."

Let `Mk` be a one-to-one market (every capacity `1`) between finite sets of men `D` and women `H`
with strict preferences over the other side and the outside option, with at least one agent.
1. For every `Φ` naming every agent infinitely often and every (a)/(b) order `ord`, DACC(Φ) stops
   in finite time and its outcome is a stable matching.
2. For every stable matching `μ` there is such a `Φ` with `μ` the outcome of DACC(Φ) for every
   (a)/(b) order.
3. A matching `μ` is stable if and only if it is the outcome of DACC(Φ) for some such `Φ` and some
   (a)/(b) order.

**Formalization Note.** Correction: DACC is Algorithm 1 (p. 8) with the stack exit of step
4(b)iii read as "µ(i) ≠ ∅ or no acceptable partner is left in Bᵢ" instead of the printed
"µ(i) ≠ ∅ or Bᵢ = ∅" (`step`); with the printed rule the first sentence is false (counterexample
in the mission description). The market is `RuralHospitals.Market` with capacity `1` (men = `D`,
women = `H`, smaller rank = better, `none` = `∅`). The (a)/(b) order of footnote a is a
universally quantified parameter `ord`. `Nonempty (D ⊕ H)` excludes only the empty market, for
which no sequence `Φ : ℕ → N` exists. The outcome is the matching of the run itself at a stopped
time (`IsOutcome`). -/
theorem theorem_1 (Mk : Market D H) (hcap : ∀ h, Mk.capacity h = 1) [Nonempty (D ⊕ H)] :
    (∀ Φ : ℕ → D ⊕ H, IsAdmissible Φ → ∀ ord : ℕ → Bool,
        ∃ μ, IsOutcome Mk Φ ord μ ∧ Mk.IsStable μ) ∧
      (∀ μ : Assignment D H, Mk.IsStable μ →
        ∃ Φ : ℕ → D ⊕ H, IsAdmissible Φ ∧ ∀ ord : ℕ → Bool, IsOutcome Mk Φ ord μ) ∧
      (∀ μ : Assignment D H, Mk.IsStable μ ↔
        ∃ (Φ : ℕ → D ⊕ H) (ord : ℕ → Bool), IsAdmissible Φ ∧ IsOutcome Mk Φ ord μ) := by sorry

end DworczakDACC
