-- Prove2me | Theorems.Thm_DGPNash_Gadget_lemma53_comparator
-- name    : DGPNash.Gadget.lemma53_comparator
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:52:05.556982+00:00
-- url     : https://prove2.me/theorems/dbc2b259-2175-4198-8ff5-efa52ebd9947
-- title:
--   Lemma 5.3 — the brittle comparator $\mathcal G_<$
-- statement:
--   Consider the binary graphical game $\mathcal G_<$ with players $a, b, d$ in which $d$ receives payoff $1$ if it plays $0$ and $a$ plays $1$, payoff $1$ if it plays $1$ and $b$ plays $1$, and $0$ otherwise, while $a$ and $b$ receive payoff $0$. Then:
--   1. the payoffs of $a$ and $b$ do not depend on the choice of $d$ ($d$ does not affect $a$ or $b$ in the sense of Definition 2.2); and
--   2. for every $0 \le \epsilon < 1$, in every $\epsilon$-Nash equilibrium of $\mathcal G_<$,
--   $$p[a] < p[b] - \epsilon \implies p[d] = 1, \qquad p[a] > p[b] + \epsilon \implies p[d] = 0 .$$
--
--   The comparator is "brittle": when $|p[a] - p[b]| \le \epsilon$ the value $p[d]$ is unconstrained. It is the gadget the reduction from Brouwer uses to extract bits from the coordinates of a point.
--
--   **Formalization Note** The paper states the lemma as "there exists a binary graphical game"; it is stated here for the explicit game given in its proof, so the existential cannot be met by a trivial game. The payoffs of $a$ and $b$ are $0$, so their mixed strategies are arbitrary at an $\epsilon$-Nash equilibrium. $\epsilon \ge 0$ is added to the paper's $\epsilon < 1$.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 245, Lemma 5.3 and its proof

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame
import Definitions.Def_DGPNash_Gadget_BasicGadgets

namespace DGPNash.Gadget

/-- Lemma 5.3 (p. 245): in the comparator game `G_<` the payoffs of `a` and `b` do not depend on
`d`, and in every ε-Nash equilibrium with `ε < 1`, `p[d] = 1` if `p[a] < p[b] − ε` and
`p[d] = 0` if `p[a] > p[b] + ε`. -/
theorem lemma53_comparator :
    ¬ Affects (S := fun _ => Fin 2) compPayoff .d .a ∧
    ¬ Affects (S := fun _ => Fin 2) compPayoff .d .b ∧
    ∀ (ε : ℝ), 0 ≤ ε → ε < 1 → ∀ σ : CompRole → Fin 2 → ℝ,
      IsEpsNash (S := fun _ => Fin 2) compPayoff ε σ →
      (σ .a 1 < σ .b 1 - ε → σ .d 1 = 1) ∧ (σ .a 1 > σ .b 1 + ε → σ .d 1 = 0) := by sorry

end DGPNash.Gadget
