-- Prove2me | Theorems.Thm_FOMCMonDep_lemma_4_10
-- name    : FOMCMonDep.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:27:52.761115+00:00
-- url     : https://prove2.me/theorems/a9c3727a-f1db-438e-ac83-bd11ea633237
-- title:
--   Lemma 4.10 — radius-$(r+h)$ definable construction sequences have radius-$r$ depth-$q$ width $O(1)\cdot\mathrm{poly}(s)$
-- statement:
--   For every $q\in\mathbb N$ there is $h\in\mathbb N$, computable from $q$, such that the following holds for every monadically dependent graph class $\mathcal C$ and all $r,c,s,q_0\in\mathbb N$. If a construction sequence of a graph $G\in\mathcal C$ is radius-$(r+h)$ definable with $c$ unary predicates, $s$ parameters and quantifier rank $q_0$, then its radius-$r$ depth-$q$ width is at most
--   $$O_{\mathcal C,q,q_0,c}(1)\cdot\mathrm{poly}_{\mathcal C,q,q_0}(s).$$
--
--   Lemma 4.10 combines Lemma 4.9 with the type bound (Theorem 4.4); together with Theorem 4.7 it yields Theorem 4.2.
--
--   **Formalization Note** $h$ is a computable function of $q$ chosen before $\mathcal C$. The bound is $A\,(s+2)^D$ with $D$ chosen after $\mathcal C,q,q_0$ and $A$ after $\mathcal C,q,q_0,c$; neither depends on $r$ or $s$.
--
--   Differences from the source:
--   - encoding: a graph class (a set of finite graphs) → MonDepMW.GraphClass, the members on each vertex set Fin n; reason: every finite graph has a copy on some Fin n, and monadic dependence and all quantities are isomorphism invariant
--   - encoding: a construction sequence G1, …, Gλ of partial graphs → the list of its λ−1 steps on colors named by naturals, from G1 with color v = v; reason: Part III's own representation with named colors; any naming of the singleton parts is equivalent
--   - encoding: O_{C,q,q0,c}(1) · poly_{C,q,q0}(s); h computable from q → A · (s + 2)^D with D after C, q, q0 and A after c; h : ℕ → ℕ with Mathlib Computable h; reason: the asymptotic convention of §3, p.11, and Mathlib's computability
--   - reading: definable by formulas of quantifier rank q0 → quantifier rank at most q0; reason: a formula of smaller rank pads to rank q0 with a dummy quantifier
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Lemma 4.10, p.15 (PDF 17)

import Mathlib
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_FOMCMonDep_RadiusDefinable

set_option autoImplicit false

namespace FOMCMonDep

/-- **Lemma 4.10.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §4.1.3, p.15 (PDF 17): "For every q ∈ N, there is h ∈ N, computable
from q, such that the following holds for every monadically dependent graph class 𝒞 and all r, c, s, q0 ∈ N. If a
construction sequence of a graph G ∈ 𝒞 is radius-(r + h) definable with c unary predicates, s parameters, and rank q0,
then its radius-r depth-q width is at most O_{𝒞,q,q0,c}(1) · poly_{𝒞,q,q0}(s)."

**Formalization Note.** `h` is a Mathlib-`Computable` function of `q`, chosen before `𝒞`. The bound is
`A · (s + 2)^D` with `D` after `𝒞, q, q₀` and `A` after `𝒞, q, q₀, c`; neither depends on `r` or `s`. Graph
classes are the published `MonDepMW.GraphClass` (members on each `Fin n`; all quantities are isomorphism invariant)
with `MonDepMW.MonadicallyDependent`. -/
theorem lemma_4_10 :
    ∃ h : ℕ → ℕ, Computable h ∧
      ∀ (q : ℕ) (𝒞 : MonDepMW.GraphClass), MonDepMW.MonadicallyDependent 𝒞 → ∀ q₀ : ℕ,
        ∃ D : ℕ, ∀ c : ℕ, ∃ A : ℕ, ∀ (r s n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
          ∀ seq : List Step, IsConstructionSeq G seq → RadiusDefinable G seq (r + h q) c s q₀ →
            depthWidth (n := n) seq r q ≤ A * (s + 2) ^ D := by sorry

end FOMCMonDep
