-- Prove2me | Theorems.Thm_BraidsLinksMCG_artin_representation_injective_step
-- name    : BraidsLinksMCG.artin_representation_injective_step
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:26:58.858898+00:00
-- url     : https://prove2.me/theorems/3b99c302-f105-492a-93bc-29870237a2c4
-- title:
--   Inductive step for faithfulness of the Artin representation
-- statement:
--   The inductive step in Artin's faithfulness theorem: if the Artin representation of the braid group on $n$ strands is faithful, so is the representation on $n+1$ strands.
--
--   The base case is elementary and is proved in the parent submission: the braid group on no strands is trivial, since its generators are indexed by the empty type, so every homomorphism out of it is injective. Induction on the number of strands then reduces the theorem to the step asserted here.
--
--   Two reductions are already available and cut the step down considerably.
--
--   First, purity is free. `BraidsLinksMCG.artin_action_trivial_perm` is proved and states that a braid acting trivially on the free group induces the trivial permutation of strands, so $\ker \xi \le \ker \pi$. A proof of the step may therefore assume from the outset that the braid under consideration is pure. The free-group input there is that conjugate generators of a free group are equal, proved by sending one generator to $1 \in \mathbb{Z}$ and the rest to $0$, conjugation being invisible in an abelian target.
--
--   Second, once purity is available the classical argument is combing. Writing $P_{n+1}$ as the kernel of the strand-forgetting map extended by a section, a pure braid factors as a free part followed by a pure braid on $n$ strands. A braid acting trivially has trivial image under the forgetting map, which by the inductive hypothesis kills the second factor; what remains is to see that the free part acts faithfully, which is a direct computation with Artin's formulas on the generators $x_1, \ldots, x_n$.
--
--   The group-theoretic half of that factorisation is available: `BraidsLinksMCG.pureBraid_ker_sup_section_eq_top` is proved, as is the explicit section `BraidsLinksMCG.pureBraid_forget_section`. What is not available is the identification of the kernel with a free group, which needs the Fadell--Neuwirth sequence together with the computation of $\pi_1$ of a punctured plane.
--
--   A caution on circularity. The statement "a pure braid acting trivially is trivial" is recorded separately as `BraidsLinksMCG.artin_faithful_on_pure_braids`, and that node has already been reduced *to* faithfulness --- the unconditional direction. With `artin_action_trivial_perm` proved the two are equivalent, so a proof of the present step must not invoke that node, on pain of circularity. The step is stated with an explicit inductive hypothesis precisely so that it is strictly more assumable than either, and can be proved without them.
-- source:
--   Artin, Theory of braids, Ann. of Math. 48 (1947); Birman, Braids, Links and Mapping Class Groups, Chapter 1, Corollary 1.8.3.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

namespace BraidsLinksMCG

theorem artin_representation_injective_step (n : ℕ)
    (ih : ∀ xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)),
      (∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w) →
        Function.Injective xi) :
    ∀ xi : ArtinBraidGroup (n + 1) →* MulAut (FreeGroup (Fin (n + 1))),
      (∀ i : Fin (n + 1 - 1), ∀ w : FreeGroup (Fin (n + 1)),
          xi (sigma i) w = artinEndo (n + 1) i w) →
        Function.Injective xi := by sorry

end BraidsLinksMCG
