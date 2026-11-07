-- Prove2me | Theorems.Thm_CodeSW_theorem_15
-- name    : CodeSW.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:25:22.094672+00:00
-- url     : https://prove2.me/theorems/532cbe51-4467-4194-8fbe-7a683a3fac5c
-- title:
--   Theorem 15 [Sin92; Gur16] — $\tau(P)\le\ln\bigl(2e/\min_S p(S)\bigr)\,O(\inf_f\rho(f))$
-- statement:
--   **Flow congestion bounds the mixing time.** There is an absolute constant $C>0$ such that the following holds for every lazy, irreducible Markov chain $P$ on a finite state space, reversible with respect to its stationary distribution $p$, and every flow $f$ for $p$: for every integer $t$ with
--   $$t\ge\ln\Bigl(\frac{2e}{\min_S p(S)}\Bigr)\,C\,\rho(f),$$
--   one has $\max_x\|P^t(x,\cdot)-p\|_{\mathrm{TV}}\le 1/(2e)$. Equivalently,
--   $$\tau(P)\le\ln\Bigl(\frac{2e}{\min_{S}p(S)}\Bigr)O\Bigl(\inf_f\rho(f)\Bigr).$$
--
--   This is the tool that turns the combinatorial flow of Theorem 16 into a mixing bound.
--
--   Differences from the source:
--   - encoding: lazy, ergodic → P(x,x) ≥ 1/2 for all x, and irreducible; reason: laziness implies aperiodicity, so this is the same class of chains
--   - encoding: O(inf_f ρ(f)) → one constant C, quantified before the state space, and the bound for every flow f; reason: a bound by C·ρ(f) for every f is a bound by C·inf_f ρ(f); the constant in O is absolute
--   - encoding: τ(P) ≤ T → for all t ≥ T, distStationary P p t ≤ 1/(2e), with an ℝ≥0∞-valued threshold; reason: total variation is half the ℓ¹ distance, d(t) is non-increasing, and an infinite congestion makes the claim empty
--   - encoding: a chain on a state space Ω → Ω ranges over `Type`; reason: an existential constant cannot be universe-polymorphic inside the statement; the paper uses it on Finset (Fin c)
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Theorem 15, p.19

import Definitions.Def_CodeSW_IsFlow
import Definitions.Def_mm_mixing
open Matrix
open scoped ENNReal

namespace CodeSW

/-- **Theorem 15 [Sin92; Gur16].** For a lazy, ergodic, reversible Markov chain `P` with
stationary law `p`, `τ(P) ≤ ln(2e / min_{S∈Ω} p(S)) · O(inf_f ρ(f))`: there is an absolute
constant `C > 0` such that for every such chain and every flow `f` for `p`, the chain is within
total variation `1/(2e)` of `p` from every start after any `t ≥ ln(2e/p_min)·C·ρ(f)` steps
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Theorem 15, p.19).

**Formalization Note** Lazy is `P(x,x) ≥ 1/2`; ergodic is irreducible (aperiodicity follows
from laziness). `C` is quantified before the state space. "`O(inf_f ρ(f))`" is the bound for
every flow `f` (equivalent). Flows and congestion are `ℝ≥0∞`-valued (Definition 14); the state
space ranges over `Type`. -/
theorem theorem_15 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω] (P : Matrix Ω Ω ℝ) (p : Ω → ℝ),
        MarkovMixing.IsStochastic P → (∀ x, 1 / 2 ≤ P x x) → MarkovMixing.Irreducible P →
        MarkovMixing.IsStationary P p → MarkovMixing.DetailedBalance P p →
        ∀ f : List Ω → ℝ≥0∞, IsFlow P p f → ∀ t : ℕ,
          ENNReal.ofReal (Real.log (2 * Real.exp 1 / ⨅ S, p S)) * ENNReal.ofReal C *
              congestion P p f ≤ (t : ℝ≥0∞) →
            MarkovMixing.distStationary P p t ≤ 1 / (2 * Real.exp 1) := by sorry

end CodeSW
