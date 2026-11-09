-- Prove2me | Theorems.Thm_DoublyEffIP_fact_1
-- name    : DoublyEffIP.fact_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:19:53.130788+00:00
-- url     : https://prove2.me/theorems/ed17cf7f-f2de-40e0-a07a-aef55262b4ff
-- title:
--   Fact 1 — a correct midpoint path from the true start states is the true midpoint matrix
-- statement:
--   Let $C$ be a set of configurations with a deterministic step function, let $k,\lambda,t\in\mathbb N$ with $0<\lambda$ and $\lambda\mid t$, let $\Phi$ be a predicate on $k\times(\lambda+1)$ matrices over $C$, and let $x=((x_{i,\mathrm{start}},x_{i,\mathrm{end}}))_{i\in[k]}$ be a batch with $x\notin L^k_t[\Phi]$. For a matrix $M^*$ consider the events
--
--   1. (F1) $\Phi(M^*)=1$;
--   2. (F2) the leftmost column of $M^*$ consists of the start states $x_{i,\mathrm{start}}$ and the rightmost column of the end states $x_{i,\mathrm{end}}$;
--   3. (F3) $x^{\nwarrow*}\in L^{k\lambda}_{t/\lambda}$, i.e. every pair of consecutive entries of a row of $M^*$ is a correct $(t/\lambda)$-step transition.
--
--   Then for every $M^*$ the three events do not hold together; in particular
--
--   $$
--   \Pr[F_1\cap F_2\cap F_3]=0 .
--   $$
--
--   This is the step of the soundness analysis of the recursive protocol Batch$(t,k)$ in which a prover-defined midpoint matrix that passes the boundary and transition checks is forced to be the true one.
--
--   Differences from the source:
--   - generalization: configurations {0,1}^S and the transition of the fixed machine M → an arbitrary type C and an arbitrary step function step : C → C; reason: the proof uses only determinism; C = {0,1}^S with M's transition is a special case
--   - generalization: t = λ^τ (assumed without loss of generality, p.20) and the case t ≥ t_base = λ (p.25) → 0 < λ and λ ∣ t; no assumption t ≥ λ; reason: weaker hypotheses; t = λ^τ with λ ≥ 1 implies them
--   - encoding: Pr[F1 ∩ F2 ∩ F3] = 0, with M* defined from the transcript → for every matrix M*, F1, F2 and F3 do not all hold; reason: M* is a function of the transcript, so the event is empty, which is probability 0 under every distribution
--   - encoding: M*[:, : S] = x[:, : S] and M*[:, −S :] = x[:, −S :]; x^{↖*} ∈ L^{kλ}_{t/λ} → column 0 of M* is the start states and column λ the end states; the kλ consecutive pairs of M*, indexed by Fin k × Fin λ, are correct (t/λ)-step transitions; reason: entries are configurations rather than their S bits; same claims
--   - encoding: Φ(M*) = 1 → Φ M* (a Prop-valued predicate); reason: same predicate
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Fact 1, Section 5.2.2, p.25

import Mathlib
import Definitions.Def_DoublyEffIP_Lkt
import Definitions.Def_DoublyEffIP_augLang
import Definitions.Def_DoublyEffIP_expandedBatch

set_option autoImplicit false

namespace DoublyEffIP

/-- **Fact 1** — Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 5.2.2, p.25.

Let `step` be a deterministic step function on configurations `C`, let `0 < λ` divide `t`, let `Φ`
be a predicate on `k × (λ + 1)` matrices, and let `x` be a batch of `k` transition claims with
`x ∉ L^k_t[Φ]`. Then for every matrix `M*` the three events
* (F1) `Φ(M*) = 1`,
* (F2) the leftmost column of `M*` is the start states of `x` and the rightmost column is its end
  states,
* (F3) `x^{↖*} ∈ L^{kλ}_{t/λ}`, i.e. consecutive entries of each row of `M*` are correct
  `t/λ`-step transitions,
do not all hold; so `Pr[F1 ∩ F2 ∩ F3] = 0` whatever the distribution of `M*`.

**Formalization Note.** Configurations form an arbitrary type with an arbitrary deterministic
step function. `M*` is a function of the transcript, so "probability 0" is "no `M*` satisfies all
three". The paper's standing assumption `t = λ^τ` (p.20) enters only as `λ ∣ t` with `0 < λ`; its
case assumption `t ≥ λ` (p.25) is not needed. -/
theorem fact_1 {C : Type*} (step : C → C) (k lam t : ℕ) (hlam : 0 < lam) (hdvd : lam ∣ t)
    (Φ : (Fin k → Fin (lam + 1) → C) → Prop) (x : Fin k → C × C)
    (hx : x ∉ augLang step t lam Φ) (Mstar : Fin k → Fin (lam + 1) → C) :
    ¬ (Φ Mstar ∧
      (∀ i, Mstar i 0 = (x i).1 ∧ Mstar i (Fin.last lam) = (x i).2) ∧
      expandedBatch Mstar ∈ Lkt step (t / lam) (Fin k × Fin lam)) := by sorry

end DoublyEffIP
