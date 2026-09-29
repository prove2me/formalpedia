-- Prove2me | Theorems.Thm_ArrowDebreu_ThmI_lemma_2_5
-- name    : ArrowDebreu.ThmI.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:39:27.409106+00:00
-- url     : https://prove2.me/theorems/08d1cd61-7bc3-401d-8c18-2e3d62dc6533
-- title:
--   Existence of an equilibrium point of an abstract economy (Lemma 2.5, Debreu 1952)
-- statement:
--   Consider an abstract economy with finitely many players $\iota$, action sets $\mathfrak A_\iota \subseteq \mathbb R^l$, pay-offs $f_\iota$ and constraint correspondences $A_\iota(\bar a_\iota) \subseteq \mathfrak A_\iota$ depending on the other players' actions $\bar a_\iota \in \bar{\mathfrak A}_\iota$. Suppose that for every player $\iota$:
--
--   1. $\mathfrak A_\iota$ is nonempty, compact and convex;
--   2. $f_\iota$ is continuous on $\mathfrak A = \prod_\iota \mathfrak A_\iota$;
--   3. for every $\bar a_\iota \in \bar{\mathfrak A}_\iota$, the function $a_\iota \mapsto f_\iota(\bar a_\iota, a_\iota)$ is quasi-concave on $\mathfrak A_\iota$;
--   4. $A_\iota$ is continuous (in the sequential sense of §2.4) at every point of $\bar{\mathfrak A}_\iota$, and its graph $\{a : \bar a_\iota \in \bar{\mathfrak A}_\iota,\ a_\iota \in A_\iota(\bar a_\iota)\}$ is closed;
--   5. for every $\bar a_\iota \in \bar{\mathfrak A}_\iota$, the set $A_\iota(\bar a_\iota)$ is convex and nonempty.
--
--   Then the abstract economy has an equilibrium point: a profile $a^* \in \mathfrak A$ with $a^*_\iota \in A_\iota(\bar a^*_\iota)$ and
--   $$f_\iota(\bar a_\iota^*, a_\iota^*) = \max_{a_\iota \in A_\iota(\bar a_\iota^*)} f_\iota(\bar a_\iota^*, a_\iota)\quad\text{for every } \iota.$$
--
--   This generalizes Nash's theorem on equilibrium points of games to the case where each player's feasible set depends on the others' actions; it is the fixed-point core of the existence proofs of Theorems I and II.
--
--   **Formalization Note** Nonemptiness of each $\mathfrak A_\iota$ is stated explicitly. The paper leaves it implicit; without it the statement fails when there are at least two players and all action sets are empty (every hypothesis then holds vacuously and there is no profile at all).
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 274 (PDF p. 11), §2.5, Lemma (a special case of Debreu, A Social Equilibrium Existence Theorem, PNAS 38 (1952) 886–893, Theorem and Remark p. 889)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

open AbstractEconomy

/-- **Lemma (§2.5)**, Arrow & Debreu, Econometrica 22 (1954), p. 274 (PDF p. 11): if, for each
`ι`, `𝔄_ι` is compact and convex, `f_ι(ā_ι, a_ι)` is continuous on `𝔄` and quasi-concave in `a_ι`
for every `ā_ι`, `A_ι(ā_ι)` is a continuous function whose graph is a closed set, and, for every
`ā_ι`, the set `A_ι(ā_ι)` is convex and non-empty, then the abstract economy has an equilibrium
point. (The paper proves it by citing Debreu, PNAS 38 (1952), p. 888, and its Remark, p. 889.)

**Formalization Note.**
* The players form a finite type `ι` (the paper's `ι = 1, ⋯, ν`); all action sets lie in `R^l`.
* "Continuous" is §2.4's sequential definition (lower hemicontinuity) at every `ā_ι ∈ 𝔄̄_ι`
  (`ConstrContinuous`); "graph closed" is closedness of `{a | ā_ι ∈ 𝔄̄_ι, a_ι ∈ A_ι(ā_ι)}` in
  `(R^l)^ι`.
* "for every `ā_ι`" ranges over `𝔄̄_ι = Π_{κ ≠ ι} 𝔄_κ` (`OthersIn`); the own coordinate of the
  profile is irrelevant (`constr_indep`), and for the pay-off it is replaced via `Function.update`.
* **Added hypothesis** `∀ ι, 𝔄_ι ≠ ∅`. The paper leaves it implicit (Debreu's action sets are
  contractible polyhedra, hence nonempty). Without it the Lemma is false for `ν ≥ 2`: if every
  `𝔄_ι` is empty, every `𝔄̄_ι` is empty, all other hypotheses hold vacuously, and `𝔄 = ∅` has no
  point. With `ν = 1` the nonemptiness of `A_1` already forces it. -/
theorem lemma_2_5 {ι : Type*} [Fintype ι] [DecidableEq ι] {l : ℕ} (G : AbstractEconomy ι l)
    (hne : ∀ i, (G.act i).Nonempty)
    (hcpt : ∀ i, IsCompact (G.act i)) (hconv : ∀ i, Convex ℝ (G.act i))
    (hcont : ∀ i, ContinuousOn (G.payoff i) G.profiles)
    (hqc : ∀ i a, G.OthersIn i a →
      QuasiconcaveOn ℝ (G.act i) (fun b => G.payoff i (Function.update a i b)))
    (hAcont : ∀ i, G.ConstrContinuous i)
    (hAgraph : ∀ i, IsClosed (G.graph i))
    (hAconv : ∀ i a, G.OthersIn i a → Convex ℝ (G.constr i a))
    (hAne : ∀ i a, G.OthersIn i a → (G.constr i a).Nonempty) :
    ∃ a, G.IsEquilibriumPoint a := by sorry

end ArrowDebreu.ThmI
