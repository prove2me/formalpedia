-- Prove2me | Theorems.Thm_FMMM_TSM_copy_reduction
-- name    : FMMM.TSM.copy_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:30:34.35688+00:00
-- url     : https://prove2.me/theorems/ed11c7fe-b5b7-4c79-831d-ba022fd73211
-- title:
--   §4.2.4, p. 9: reduction to $e_i = 1$ ($\mathrm{OPT}' = \mathrm{OPT}$)
-- statement:
--   Let $E$ be the edges between ads $A$ and impression types $I$, with integers $e_i \ge 0$ and $n = \sum_i e_i$, and let $G'$ be the copy instance: $e_i$ copies of each type $i$, each copy adjacent to the neighbours of its type. Let $\omega_0, \dots, \omega_{n-1}$ be draws of copies, and $\tau_t$ the type of the copy $\omega_t$.
--
--   1. For every sequence of copies, the maximum matching of the realization graph of $G'$ equals the maximum matching of the realization graph of $G$ on the types: $\mathrm{OPT}'(\omega) = \mathrm{OPT}(\tau)$.
--   2. If the copies are drawn i.i.d. uniformly, the types are drawn i.i.d. from $D$, $\Pr[i] = e_i/n$: for every sequence of types $\tau$,
--   $$\Pr[\text{the types of the draws are } \tau_0, \dots, \tau_{n-1}] = \prod_{t=0}^{n-1} \frac{e_{\tau_t}}{n}.$$
--
--   This justifies applying the case $e_i = 1$ to the copy instance: drawing a type from $D$ and naming it uniformly among its copies is the same as drawing a copy uniformly, and the optimum does not change.
--
--   Differences from the source:
--   - encoding: draw a type i ∼ D, then name it uniformly at random as one of its e_i copies → draw a copy uniformly from the n copies (unifProb over Copy e); reason: the two procedures give the same joint law of (type, name); part 2 states the type marginal
--   - encoding: n i.i.d. uniform draws (balls into bins) → the counting probability unifProb on sequences Fin n → Ω, draws indexed 0, …, n − 1; reason: the uniform measure on Ωⁿ is the law of n i.i.d. uniform draws; same probabilities
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.4, p. 9 (reduction for integer e_i)

import Mathlib
import Definitions.Def_FMMM_TSM_unifProb
import Definitions.Def_FMMM_TSM_realOPT
import Definitions.Def_FMMM_TSM_Copy
import Definitions.Def_FMMM_TSM_copyEdges

namespace FMMM.TSM

/-- **The reduction to `e_i = 1`: `OPT′ = OPT`, and the named draws have law `D`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.4, p. 9: "Given a set of instance Γ = (G, D, n), we reduce to a new instance
Γ′ = (G′, D′, n) with e′_i = 1 by making e_i copies of each impression type i. Then, when an
impression of type i arrives online, "name" it randomly according to one of its copies. The
resulting distribution D′ is uniform over the impression types I′ in the new instance. Let Î be
the impressions that are drawn from D in one run of the algorithm, and let Î′ be the resulting draws
from D′. By the arguments above, we achieve the desired bound on ALG/OPT′ with high probability,
where OPT′ is with respect to Î′; however we have OPT′ = OPT, since the realization graphs
Ĝ = (A, Î′, Ê′) and Ĝ′ = (A, Î, Ê) are in fact the same graph."

Let `E` have impression types `I` with integers `e : I → ℕ` and `n = ∑ e_i`.
1. For every sequence `ω` of `n` named draws (copies), the maximum matching of the copy
   realization graph equals that of the original one: `OPT′(ω) = OPT(types ω)`.
2. Under uniform named draws, the types are i.i.d. `D`: for every `τ : Fin n → I`,
   `Pr[types ω = τ] = ∏_t e_{τ t}/n`. -/
theorem copy_reduction {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E : Finset (A × I)) (e : I → ℕ) :
    (∀ ω : Fin (∑ i, e i) → Copy e,
      realOPT (copyEdges E e) ω = realOPT E (fun t => (ω t).1)) ∧
    ∀ τ : Fin (∑ i, e i) → I,
      unifProb (Copy e) (∑ i, e i) (fun ω => (fun t => (ω t).1) = τ) =
        ∏ t, (e (τ t) : ℝ) / ((∑ i, e i : ℕ) : ℝ) := by sorry

end FMMM.TSM
