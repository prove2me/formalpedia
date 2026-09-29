-- Prove2me | Theorems.Thm_AKSSorting_Core_halver_property
-- name    : AKSSorting.Core.halver_property
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T10:05:04.51765+00:00
-- url     : https://prove2.me/theorems/850c01a3-71bd-46f7-a798-22961ff90900
-- title:
--   Lemma 4 — one round of expander comparisons is an ε-halver
-- statement:
--   Let $A$ and $B$ be disjoint sets of registers, $\varepsilon>0$, and let $G$ be a $\langle k,\varepsilon\rangle$ expander on $\langle A,B\rangle$ for some $k$. Let $E_\varepsilon(A,B)$ be the set of elementary steps "if the content of $a$ is greater than the content of $b$, exchange them", one for each edge $\{a,b\}$ of $G$ with $a\in A$, $b\in B$. Start from an injective assignment of contents to registers and perform all steps of $E_\varepsilon(A,B)$, each exactly once, in an arbitrary order. Write $\mathrm{Cont}(X)$ for the set of final contents of the registers in $X$. Then:
--
--   1. if $S$ is a lower section of $\mathrm{Cont}(A\cup B)$ with $|S|\le|A|$, then
--   $$ |S\setminus\mathrm{Cont}(A)|\le\varepsilon|S|; $$
--   2. if $S$ is an upper section of $\mathrm{Cont}(A\cup B)$ with $|S|\le|B|$, then $|S\setminus\mathrm{Cont}(B)|\le\varepsilon|S|$.
--
--   So after one round, all but an $\varepsilon$-fraction of any initial segment of small elements sits in $A$, and symmetrically for large elements in $B$. This approximate halving is the only use of expanders in the AKS network.
--
--   **Formalization Note** The order of the steps is a list `steps` whose members are exactly the pairs $(a,b)$ with $a\in A$, $b\in B$ adjacent in $G$, without repetitions; the conclusion must hold for every such list. The lemma is stated for every expander $G$ with any degree bound, which covers the paper's fixed choice $G_\varepsilon(A,B)$. Contents come from an arbitrary linearly ordered type and the initial position is injective, as in the paper's "one-to-one map of $\mathcal R$ onto $L$".
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), p. 7, Lemma 4 (proof p. 9); p. 6, Definitions 3.1-3.3

import Mathlib
import Definitions.Def_AKSSorting_Core_compareExchange
import Definitions.Def_AKSSorting_Core_IsExpander
import Definitions.Def_AKSSorting_Core_IsLowerSection

namespace AKSSorting.Core

/-- Lemma 4 (Ajtai–Komlós–Szemerédi 1983, p. 7; proved on p. 9). Let `A, B` be disjoint sets of
registers, `ε > 0`, and `G` any `⟨k, ε⟩` expander on `⟨A, B⟩`. Perform every elementary step
of `E_ε(A, B)` — for every edge `{a, b}` of `G` with `a ∈ A`, `b ∈ B`, the compare-exchange that
leaves the smaller content in `a` — exactly once, in an arbitrary order `steps`, starting from
the position `F`. With `F'` the resulting position:
* if `S` is a lower section of `Cont(A ∪ B)` with `|S| ≤ |A|`, then `|S − Cont(A)| ≤ ε|S|`;
* if `S` is an upper section of `Cont(A ∪ B)` with `|S| ≤ |B|`, then `|S − Cont(B)| ≤ ε|S|`. -/
theorem halver_property {R : Type} [DecidableEq R] {α : Type} [LinearOrder α]
    (A B : Finset R) (hAB : Disjoint A B) (ε : ℝ) (hε : 0 < ε) (k : ℕ) (G : SimpleGraph R)
    (hG : IsExpander G A B k ε) (steps : List (R × R))
    (hsteps : ∀ p : R × R, p ∈ steps ↔ (p.1 ∈ A ∧ p.2 ∈ B ∧ G.Adj p.1 p.2))
    (hnodup : steps.Nodup) (F : R → α) (hF : Function.Injective F) :
    let F' := steps.foldl (fun x p => compareExchange p.1 p.2 x) F
    (∀ S : Finset α, IsLowerSection ((A ∪ B).image F') S → S.card ≤ A.card →
        ((S \ A.image F').card : ℝ) ≤ ε * S.card) ∧
    (∀ S : Finset α, IsUpperSection ((A ∪ B).image F') S → S.card ≤ B.card →
        ((S \ B.image F').card : ℝ) ≤ ε * S.card) := by sorry

end AKSSorting.Core
