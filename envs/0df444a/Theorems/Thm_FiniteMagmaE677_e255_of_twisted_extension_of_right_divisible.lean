-- Prove2me | Theorems.Thm_FiniteMagmaE677_e255_of_twisted_extension_of_right_divisible
-- name    : FiniteMagmaE677.e255_of_twisted_extension_of_right_divisible
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-23T01:10:20.347289+00:00
-- url     : https://prove2.me/theorems/8822e622-3a07-4605-a54a-81a1e5b87f77
-- title:
--   Counterexample structure (n) — Extensions twisted by automorphisms of the fibre satisfy E255 when the fibre satisfies condition (R)
-- statement:
--   Let $Q$ and $E$ be finite sets with operations $\diamond_Q$ and $\diamond_E$, and let $\diamond$ be an operation on $Q\times E$. The block $(x,y)$ is the part of the table of $\diamond$ with rows in $\{x\}\times E$ and columns in $\{y\}\times E$. It is twisted when there are automorphisms $\varphi_{x,y},\psi_{x,y}$ of $(E,\diamond_E)$ with
--
--   $$(x,s)\diamond(y,t)=(x\diamond_Q y,\;\varphi_{x,y}(s)\diamond_E\psi_{x,y}(t))\quad\text{for all } s,t\in E.$$
--
--   The fibre $(E,\diamond_E)$ satisfies condition (R) when, for all automorphisms $\alpha,a,b,c$ of $(E,\diamond_E)$ with
--
--   $$s=t\diamond_E\bigl(\alpha(s)\diamond_E((a(t)\diamond_E b(s))\diamond_E c(t))\bigr)\quad\text{for all } s,t\in E,$$
--
--   the equation $r\diamond_E b(s)=a(s)$ has a solution $r\in E$ for every $s\in E$. (For $\alpha=a=b=c=\mathrm{id}$ this identity is E677 for $\diamond_E$.)
--
--   **Theorem.** Suppose that
--
--   1. $(Q\times E,\diamond)$ satisfies E677, and $(Q,\diamond_Q)$ satisfies E255;
--   2. every block is twisted, except that the blocks $(e,e)$ with $e\diamond_Q e=e$ (the idempotent diagonal blocks) may have any table;
--   3. E255 holds at every point $(e,s)$ with $e\diamond_Q e=e$;
--   4. $(E,\diamond_E)$ satisfies (R).
--
--   Then $(Q\times E,\diamond)$ satisfies E255. E677 is not assumed for $\diamond_Q$ or for $\diamond_E$.
--
--   **Which fibres satisfy (R).** By Counterexample structure (o), (R) holds when $E$ is rigid and satisfies E255, and when $E$ is right-cancellative (see (o) for the terms). Counterexample structure (p) treats a right-cancellative fibre with permutations in place of automorphisms.
--
--   **Use in a counterexample search.** Let $\theta$ be a congruence of a minimum counterexample $M$ that is neither equality nor universal. All $\theta$-classes have the same size (as used in Counterexample structure (b)), so $M$ can be written as $Q\times E$ with $Q=M/\theta$. By minimality, $Q$ satisfies E255, and so does each class over an idempotent of $Q$ (a smaller submagma). So hypotheses 1 and 3 hold, and the blocks of $M$ off the idempotent diagonal blocks are not all twisted for one fibre operation with (R).
--
--   **Prior work.** ETP blueprint Lemma 13.4 proves E255 for the affine extensions $(x,s)\diamond(y,t)=(x\diamond y,\alpha_{x,y}s+\beta_{x,y}t+c_{x,y})$ over an abelian group, with endomorphisms $\alpha_{x,y},\beta_{x,y}$. The twisted form has a magma in place of the abelian group, automorphisms in place of the endomorphisms, and no constant term. The twisted construction is B. Le Floch's (ETP Zulip thread "FINITE: 677 -> 255", 2024-12-18): $(x,s)\diamond(y,t)=(x\diamond y,S_{x,y}(s)\diamond T_{x,y}(t))$ with endomorphisms $S_{x,y},T_{x,y}$ of the fibre, $T_{x,y}$ bijective; here both twists are bijective. The same day he gave an informal argument that it gives no finite counterexample, and then noted: "If M is not right-invertible to begin with ..., then the result is not right-invertible." On 2024-12-25 he wrote that for this construction "there was no direct immunity to 677->255". This theorem adds a Lean proof, arbitrary idempotent diagonal blocks, and condition (R), which does not require right cancellation and holds for the rigid fibres with E255 of (o). It was not found in the ETP blueprint, the ETP paper (arXiv:2512.07087v2) or the ETP Zulip thread up to 2026-10-14.
--
--   **Formalization Note** The operations are `opQ`, `opE` and `op` on `Q × E`. The twists are maps `φ ψ : Q → Q → Equiv.Perm E`, and `hφ`, `hψ` say that they respect `opE`. `htw` says that every block `(x, y)` with `¬ (x = y ∧ opQ x x = x)` is twisted. `hidem` is hypothesis 3, and `hR` is (R) with the automorphism property written out. The theorem is about the product type; a magma that is only isomorphic to a product needs a transport step that is not part of this statement.
-- source:
--   Adam McKenna, 2026-10-20

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u v
open FiniteMagmaE677

theorem FiniteMagmaE677.e255_of_twisted_extension_of_right_divisible
{Q : Type u} {E : Type v} [Finite Q] [Finite E]
(opQ : Q → Q → Q) (opE : E → E → E) (op : Q × E → Q × E → Q × E)
(φ ψ : Q → Q → Equiv.Perm E)
(hQ : FiniteMagmaE677.E255 opQ) (h : FiniteMagmaE677.E677 op)
(htw : ∀ (x y : Q) (s t : E), ¬ (x = y ∧ opQ x x = x) →
  op (x, s) (y, t) = (opQ x y, opE (φ x y s) (ψ x y t)))
(hidem : ∀ x : Q, opQ x x = x → ∀ s : E,
  (x, s) = op (op (op (x, s) (x, s)) (x, s)) (x, s))
(hφ : ∀ (x y : Q) (a b : E), φ x y (opE a b) = opE (φ x y a) (φ x y b))
(hψ : ∀ (x y : Q) (a b : E), ψ x y (opE a b) = opE (ψ x y a) (ψ x y b))
(hR : ∀ α a b c : Equiv.Perm E,
  (∀ u w : E, α (opE u w) = opE (α u) (α w)) →
  (∀ u w : E, a (opE u w) = opE (a u) (a w)) →
  (∀ u w : E, b (opE u w) = opE (b u) (b w)) →
  (∀ u w : E, c (opE u w) = opE (c u) (c w)) →
  (∀ s t : E, s = opE t (opE (α s) (opE (opE (a t) (b s)) (c t)))) →
  ∀ s : E, ∃ r : E, opE r (b s) = a s) :
FiniteMagmaE677.E255 op := by sorry
