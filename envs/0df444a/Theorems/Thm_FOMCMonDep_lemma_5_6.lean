-- Prove2me | Theorems.Thm_FOMCMonDep_lemma_5_6
-- name    : FOMCMonDep.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:35.98822+00:00
-- url     : https://prove2.me/theorems/3a9a13ff-ae6f-4369-a316-4a42a921d7dc
-- title:
--   Lemma 5.6 — a polynomial superset $A^*$: balls of $s$-definable flips avoiding $A^*$ meet at most $t$ atomic types over $A$
-- statement:
--   Let $\mathcal C$ be a monadically dependent class of (possibly infinite) graphs and $r,s\in\mathbb N$. There are $k,t\in\mathbb N$ such that for every $G\in\mathcal C$ and every finite $A\subseteq V(G)$ there is a set $A^*\supseteq A$ of size $O_{\mathcal C,r,s}(|A|^k)$ with the following property: for every $s$-definable flip $H$ of $G$ and every vertex $v$,
--   $$\mathrm{Ball}^H_r(v)\cap A^*=\emptyset\ \Longrightarrow\ \bigl|\mathrm{ATypes}^H(\mathrm{Ball}^H_r(v)/A)\bigr|\le t .$$
--   Equivalently, a radius-$r$ ball of $H$ that avoids $A^*$ meets at most $t$ parts of the partition of $V(G)$ into atomic types over $A$ in $H$.
--
--   This is the first of the two lemmas behind the Closure Theorem (Theorem 5.1); $s$ is an input of the lemma, which avoids a cyclic dependency in the induction on $r$.
--
--   **Formalization Note** $O_{\mathcal C,r,s}(|A|^k)$ is $a|A|^k+b$ with $a,b$ chosen after $\mathcal C,r,s$ and before $G$.
--
--   Differences from the source:
--   - encoding: a monadically dependent class of possibly infinite graphs (Part I) → AnyGraphClass (members on every vertex type) with MonDepAny; reason: the paper's definition with the witness graph on any type; Part I allows infinite graphs
--   - encoding: s-definable flip G ⊕ (p̄, R) → an S-flip for some finite S with |S| ≤ s (IsSDefFlip); reason: the equivalent form printed on p.18
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Lemma 5.6, p.18 (PDF 20)

import Mathlib
import Definitions.Def_FOMCMonDep_tp
import Definitions.Def_FOMCMonDep_IsPFlip
import Definitions.Def_FOMCMonDep_MonDepAny

set_option autoImplicit false

namespace FOMCMonDep

/-- **Lemma 5.6.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §5.2, p.18 (PDF 20); proof §5.3: "For every monadically dependent
graph class 𝒞 and r, s ∈ N, there are some k, t ∈ N with the following property. For every G ∈ 𝒞 and finite set
A ⊆ V(G), there is A* ⊇ A of size O_{𝒞,r,s}(|A|^k) such that, for every s-definable flip H of G and every vertex v,
Ball^H_r(v) ∩ A* = ∅ =⇒ |ATypes^H(Ball^H_r(v)/A)| ⩽ t."

**Formalization Note.** Part I: graphs may be infinite (p.17), so `𝒞` is an `AnyGraphClass` with `MonDepAny`.
`O_{𝒞,r,s}(|A|^k)` is `a · |A|^k + b` with `a, b` chosen after `𝒞, r, s` (and `k, t`), before `G` (§3, p.11); `A*`
is finite, so `ncard` is its size. `|ATypes^H(X/A)| = |Types^H_{1,0}(X/A)|` is `typeCount H.structure 1 0 X A`, an
`encard`. -/
theorem lemma_5_6 (𝒞 : AnyGraphClass) (h𝒞 : MonDepAny 𝒞) (r s : ℕ) :
    ∃ k t : ℕ, ∃ a b : ℕ, ∀ (V : Type) (G : SimpleGraph V), G ∈ 𝒞 V → ∀ A : Set V, A.Finite →
      ∃ Astar : Set V, A ⊆ Astar ∧ Astar.Finite ∧ Astar.ncard ≤ a * A.ncard ^ k + b ∧
        ∀ H : SimpleGraph V, IsSDefFlip G s H → ∀ v : V,
          ballSet H r {v} ∩ Astar = ∅ → typeCount H.structure 1 0 (ballSet H r {v}) A ≤ t := by sorry

end FOMCMonDep
