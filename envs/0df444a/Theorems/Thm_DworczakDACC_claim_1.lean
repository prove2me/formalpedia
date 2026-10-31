-- Prove2me | Theorems.Thm_DworczakDACC_claim_1
-- name    : DworczakDACC.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:54.681147+00:00
-- url     : https://prove2.me/theorems/2e88461e-ee29-4942-aed0-402fab36dcb2
-- title:
--   Claim 1 — if DACC stops, the outcome is stable (corrected: stack exit when no acceptable partner remains)
-- statement:
--   Let the market be one-to-one. For every order $\Phi$, every order of blocks (a)/(b) and every time $t$: if the run of DACC($\Phi$) satisfies the stopping criterion at time $t$, then the matching at time $t$ is **stable**: it is a one-to-one matching, every agent is matched to an acceptable partner or unmatched, and there is no man $d$ and woman $h$ with
--
--   $$h\succ^d\mu(d)\quad\text{and}\quad d\succ^h\mu(h).$$
--
--   This is the sufficiency half of Theorem 1: whenever DACC stops, it stops at a stable matching.
--
--   Differences from the source:
--   - encoding: men M, women W, strict preferences ≻ⁱ on Nᵢ ∪ {∅}, matching and stability as on p. 5 → RuralHospitals.Market D H with capacity h = 1 for all h (men = D, women = H, injective ranks with smaller = better, none = ∅); Market.IsStable; reason: with capacity 1, IsStable is exactly p. 5's stability (one-to-one, acceptable partners, j ≻ⁱ µ(i) ⇒ µ(j) ≻ʲ i); same instances
--   - generalization: Φ takes every value in N infinitely often (standing assumption, p. 6) → Φ : ℕ → D ⊕ H arbitrary; reason: the state at any time t depends on finitely many values of Φ, and every finite prefix extends to an order taking every value infinitely often; the statement specializes to admissible Φ
--   - generalization: items (a) and (b) of "i applies" executed in some order (footnote a, p. 8: "in any order, even random") → the order is a parameter ord : ℕ → Bool (one choice per time step), universally quantified; reason: every resolution of footnote a, including a random one along each sample path, is some ord
--   - correction: Algorithm 1, step 4(b)iii (p. 8): remove i from CC if µ(i) ≠ ∅ or Bᵢ = ∅ → remove i from CC if µ(i) ≠ ∅ or argmax{Bᵢ ∪ {∅}; ≻ⁱ} = ∅ (no acceptable partner left in Bᵢ); reason: budgets start full and unacceptable partners never leave them, so a compensated agent with no acceptable partner left applies to ∅ forever under the printed test; in the market m1: w2; m2: w2 ≻ w1; m3: w3 ≻ w1; w1: m2 ≻ m3 ≻ m1; w2: m3 ≻ m1 ≻ m2; w3: nobody, with Φ = m2, w1, m1, w1, (m1, m2, m3, w1, w2, w3) repeated, m3 is stuck on CC from round 6 on and DACC never stops; the corrected test is the paper's own footnote 7 convention and coincides with the printed one when every partner is acceptable; the printed algorithm's run agrees with the corrected run until a compensated agent is stuck, and then stays in a non-stopped state forever, so every stopped state of the printed run is a stopped state of the corrected run and the claim transfers
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Claim 1, p. 7

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_Stopped
import Definitions.Def_DworczakDACC_run

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **Claim 1: if DACC stops, the outcome is stable.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), Claim 1,
p. 7: "If DACC stops, the outcome is stable."

In a one-to-one market (every capacity `1`), for every order `Φ`, every (a)/(b) order `ord` and
every time `t`: if the stopping criterion holds in `run Mk Φ ord t`, then the matching of that
state is stable (`Market.IsStable`: a matching, individually rational, without a blocking pair).

**Formalization Note.** Men are `D`, women `H`, smaller rank is better, `none` is `∅`; with
capacity `1`, `Market.IsStable` is the stability of p. 5. `Φ` is arbitrary (a generalization of
the paper's standing assumption; every finite prefix extends to an admissible order). The run is
that of the algorithm with the corrected stack exit; the claim does not depend on the exit rule. -/
theorem claim_1 (Mk : Market D H) (hcap : ∀ h, Mk.capacity h = 1) (Φ : ℕ → D ⊕ H)
    (ord : ℕ → Bool) (t : ℕ) (hstop : Stopped Mk (run Mk Φ ord t)) :
    Mk.IsStable (run Mk Φ ord t).mateM := by sorry

end DworczakDACC
