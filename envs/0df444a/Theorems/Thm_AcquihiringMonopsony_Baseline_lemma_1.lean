-- Prove2me | Theorems.Thm_AcquihiringMonopsony_Baseline_lemma_1
-- name    : AcquihiringMonopsony.Baseline.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:50.074125+00:00
-- url     : https://prove2.me/theorems/1ff89a35-de70-4653-adfd-a91672ccb758
-- title:
--   Lemma 1 — under direct hiring the acquirer hires at v_s + b if v_a > v_s + b, else the startup retains at v_a − b; efficient
-- statement:
--   Consider the baseline model with values $v_a, v_s$, private benefit $b$ and wage floor $\underline{w}$, satisfying $b > 0$ and $\min\{v_a, v_s\} > b + \underline{w}$. Suppose the acquirer chooses direct hiring, so that the acquirer and the startup compete in wages for the employee.
--
--   Then in every continuation equilibrium in undominated strategies, with equilibrium offers $w_a$ and $w_s$:
--   1. if $v_a > v_s + b$, the acquirer hires the employee, at wage $w_a = v_s + b$;
--   2. if $v_a < v_s + b$, the startup retains the employee, at wage $w_s = v_a - b$;
--   3. the outcome is efficient, i.e. its total surplus is
--   $$
--   \max\{v_a,\ v_s + b\}.
--   $$
--   Moreover, when $v_a \neq v_s + b$, such a continuation equilibrium exists.
--
--   This is the asymmetric Bertrand outcome of the wage competition: the firm with the higher willingness to pay (counting the employee's private benefit in the startup's favour) wins her at the rival's reservation level. It determines the acquirer's and the employee's payoffs from direct hiring, which Proposition 1 compares with acquihiring.
--
--   **Formalization Note.** Uniqueness of the outcome is stated for every equilibrium profile, including the employee's acceptance rule off the path. The existence clause is the reading of "the continuation equilibrium" on the page; the knife edge $v_a = v_s + b$, which the lemma does not cover, is excluded from it, while the efficiency clause is stated there as well.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 5 (PDF 6), Lemma 1

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model

namespace AcquihiringMonopsony.Baseline

/-- Lemma 1 (p. 5): under direct hiring, in every continuation equilibrium the acquirer hires
the employee at wage `v_s + b` if `v_a > v_s + b`, the startup retains her at wage `v_a − b`
if `v_a < v_s + b`, and the outcome maximizes total surplus; a continuation equilibrium exists
whenever `v_a ≠ v_s + b`. -/
theorem lemma_1 (P : Params) (hP : P.Standing) :
    (∀ σ : DHProfile, IsDHEquilibrium P σ →
      (P.vs + P.b < P.va → σ.acceptA σ.wa σ.ws = true ∧ σ.wa = P.vs + P.b) ∧
      (P.va < P.vs + P.b → σ.acceptA σ.wa σ.ws = false ∧ σ.ws = P.va - P.b) ∧
      surplus P (σ.acceptA σ.wa σ.ws) = max P.va (P.vs + P.b)) ∧
    (P.va ≠ P.vs + P.b → ∃ σ : DHProfile, IsDHEquilibrium P σ) := by sorry

end AcquihiringMonopsony.Baseline
