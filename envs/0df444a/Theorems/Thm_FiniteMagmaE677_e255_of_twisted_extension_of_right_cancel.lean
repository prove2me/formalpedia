-- Prove2me | Theorems.Thm_FiniteMagmaE677_e255_of_twisted_extension_of_right_cancel
-- name    : FiniteMagmaE677.e255_of_twisted_extension_of_right_cancel
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-23T01:13:13.303085+00:00
-- url     : https://prove2.me/theorems/10bc5f4e-1a8e-4815-a6cb-23c89c9e2ae5
-- title:
--   Counterexample structure (p) — Extensions twisted by permutations over a finite right-cancellative fibre satisfy E255
-- statement:
--   Let $Q$ and $E$ be finite sets with operations $\diamond_Q$ and $\diamond_E$, and let $\diamond$ be an operation on $Q\times E$, with blocks as in Counterexample structure (n). The block $(x,y)$ is permutation-twisted when there are permutations $\varphi_{x,y},\psi_{x,y}$ of $E$ with
--
--   $$(x,s)\diamond(y,t)=(x\diamond_Q y,\;\varphi_{x,y}(s)\diamond_E\psi_{x,y}(t))\quad\text{for all } s,t\in E.$$
--
--   $(E,\diamond_E)$ is right-cancellative when $a\diamond_E b=a'\diamond_E b$ gives $a=a'$.
--
--   **Theorem.** Suppose that
--
--   1. $(Q\times E,\diamond)$ satisfies E677, and $(Q,\diamond_Q)$ satisfies E255;
--   2. every block is permutation-twisted, except that the blocks $(e,e)$ with $e\diamond_Q e=e$ (the idempotent diagonal blocks) may have any table;
--   3. E255 holds at every point $(e,s)$ with $e\diamond_Q e=e$;
--   4. $(E,\diamond_E)$ is right-cancellative.
--
--   Then $(Q\times E,\diamond)$ satisfies E255. No equation on $E$, no equation on $Q$ other than E255, and no property of the twists other than bijectivity is assumed.
--
--   **Proof idea.** Let $(x,s)\in Q\times E$ with $x\diamond_Q x\ne x$, and let $v=(x\diamond_Q x)\diamond_Q x$, so $v\diamond_Q x=x$ by E255 in $Q$. The block $(v,x)$ is permutation-twisted, and $a\mapsto\varphi_{v,x}(a)\diamond_E\psi_{v,x}(s)$ is injective on the finite set $E$, so it is onto: some $(v,a)$ satisfies $(v,a)\diamond(x,s)=(x,s)$. In a finite E677 magma, such an element gives E255 at $(x,s)$ (ETP blueprint, Lemma 13.2). The points over an idempotent are hypothesis 3.
--
--   **Use in a counterexample search.** In a minimum counterexample, hypotheses 1 and 3 hold for every congruence that is neither equality nor universal (see (n)). So over a finite right-cancellative fibre, no choice of permutation twists off the idempotent diagonal blocks gives a minimum counterexample.
--
--   **Prior work.** The construction is B. Le Floch's (ETP Zulip thread "FINITE: 677 -> 255", 2024-12-18), with endomorphisms $S_{x,y},T_{x,y}$ of the fibre as twists, $T_{x,y}$ bijective. The proof above is the fixer argument of the proof of ETP blueprint Lemma 13.4 (affine extensions; B. Le Floch, same thread, 2024-12-14), with right cancellation in $E$ in place of the injectivity of the affine map. This theorem adds a Lean proof, twists that are any permutations (with no morphism property; here both twists are bijective), a base $Q$ that satisfies only E255 (no right cancellation), and arbitrary idempotent diagonal blocks.
--
--   **Formalization Note** The twists are maps `φ ψ : Q → Q → Equiv.Perm E` with no further property. `htw` says that every block `(x, y)` with `¬ (x = y ∧ opQ x x = x)` is permutation-twisted, `hidem` is hypothesis 3, and `hrc` says that every right multiplication of `opE` is injective. The theorem is about the product type; a magma that is only isomorphic to a product needs a transport step that is not part of this statement.
-- source:
--   Adam McKenna, 2026-10-20

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u v
open FiniteMagmaE677

theorem FiniteMagmaE677.e255_of_twisted_extension_of_right_cancel
{Q : Type u} {E : Type v} [Finite Q] [Finite E]
(opQ : Q → Q → Q) (opE : E → E → E) (op : Q × E → Q × E → Q × E)
(φ ψ : Q → Q → Equiv.Perm E)
(hQ : FiniteMagmaE677.E255 opQ) (h : FiniteMagmaE677.E677 op)
(htw : ∀ (x y : Q) (s t : E), ¬ (x = y ∧ opQ x x = x) →
  op (x, s) (y, t) = (opQ x y, opE (φ x y s) (ψ x y t)))
(hidem : ∀ x : Q, opQ x x = x → ∀ s : E,
  (x, s) = op (op (op (x, s) (x, s)) (x, s)) (x, s))
(hrc : ∀ b : E, Function.Injective (fun a : E => opE a b)) :
FiniteMagmaE677.E255 op := by sorry
