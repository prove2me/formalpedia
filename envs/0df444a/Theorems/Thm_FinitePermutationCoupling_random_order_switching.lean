-- Prove2me | Theorems.Thm_FinitePermutationCoupling_random_order_switching
-- name    : FinitePermutationCoupling.random_order_switching
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T18:27:46.628369+00:00
-- url     : https://prove2.me/theorems/6dde3d42-84d5-4f01-8545-97d2ef4b6f90
-- title:
--   Random-order correction coupling from conditional partner bounds
-- statement:
--   Let $A$ be finite and let $b:A\to K$ partition it into classes. Let $P_b$ be the permutations preserving these classes, and designate some classes as active. Let $S\subseteq P_b$ be nonempty. Assume membership in $S$ depends only on the images of active inputs. For every exposed assignment, assume that an unexposed input in an active class with $r\ge2$ remaining inputs has each conditional partner probability at most $1/(r-1)$ under the uniform law on $S$.
--
--   Let $N>0$ bound the size of every active class. There is a nonnegative joint weight $v(h,p)$ on reference permutations and paths $p:\{0,\ldots,N\}\to\operatorname{Perm}(A)$ with reference marginal uniform on $S$, terminal value $p(N)=h$ on its support, and initial marginal $p(0)$ uniform on $P_b$. For every fixed reference $h$, input $x$, and $0\le i<N$,
--   $$\sum_p v(h,p)\mathbf1[p(i)(x)\ne p(i+1)(x)]\le\frac{2}{|C(x)|(i+1)}\rho_S(h)$$
--   when the class $C(x)$ is active; the left side is zero for inactive classes. The cap is stated by completion counts, including empty conditioning fibers and singleton residual classes.
--
--   This is the abstract finite stochastic construction in the random-order correction argument. Its hypotheses contain all source-specific combinatorics. Classes smaller than $N$ have identity padding. Stages may be recorded jointly across the disjoint active classes after their sequential histories have been sampled.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S4.SS4, Section 4.4, proof of Lemma 4.13, equations (76)--(77) and the three-step random-order correction process between them. Generalization of the source construction to finite class-preserving permutations. Active saturation makes all inactive class coordinates independent uniform permutations. The conditional-count assumption is exactly the input used to make each residual kernel nonnegative; the source proof then gives uniform output and the conditional fixed-reference stage bound 2/(m r). No graph-specific counting, size estimate, oracle, or quantum claim is assumed or concluded.

import Definitions.Def_FinitePermutationCoupling_BlockModel

namespace FinitePermutationCoupling

open Classical
open scoped BigOperators

/-- Abstract random-order residual-kernel construction from the proof of
Lemma 4.13, arXiv:2611.05912v1, Section 4.4, equations (76)--(77). -/
theorem random_order_switching
    {α κ : Type*} [Fintype α] (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (N : ℕ)
    (hN : 0 < N) (hS : S.Nonempty) (hsub : S ⊆ blockSupport block)
    (hsat : ActiveSaturated block active S)
    (hcap : PartnerCap block active S)
    (hsize : ∀ x, active (block x) → (blockFiber block x).card ≤ N) :
    ∃ v : Equiv.Perm α → (Fin (N + 1) → Equiv.Perm α) → ℝ,
      (∀ h p, 0 ≤ v h p) ∧
      (∀ h, (∑ p, v h p) = density S h) ∧
      (∀ h p, v h p ≠ 0 → p (Fin.last N) = h) ∧
      (∀ g, (∑ h, ∑ p, if p 0 = g then v h p else 0) =
        density (blockSupport block) g) ∧
      (∀ h (x : α) (i : Fin N),
        (∑ p, if (p i.castSucc) x ≠ (p i.succ) x then v h p else 0) ≤
          (if active (block x) then
            2 / (((blockFiber block x).card : ℝ) * ((i.val : ℝ) + 1))
          else 0) * density S h) := by
  sorry

end FinitePermutationCoupling
