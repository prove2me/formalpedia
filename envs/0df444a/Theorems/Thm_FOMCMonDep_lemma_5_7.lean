-- Prove2me | Theorems.Thm_FOMCMonDep_lemma_5_7
-- name    : FOMCMonDep.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:30.372607+00:00
-- url     : https://prove2.me/theorems/8dfaadfc-e6bd-45a7-aa91-50ecab67916c
-- title:
--   Lemma 5.7 — few atomic types around $C$ give a $z$-definable flip separating $C$ from $A$ at radius $r+1$
-- statement:
--   For all $d,t\in\mathbb N$ there is $z\in\mathbb N$ such that the following holds. Let $G$ be a graph of VC-dimension at most $d$, $r\in\mathbb N$, $A\subseteq V(G)$ finite and $C\subseteq V(G)$ arbitrary, with
--   $$\mathrm{Ball}^G_r(C)\cap A=\emptyset\qquad\text{and}\qquad \bigl|\mathrm{ATypes}^G(\mathrm{Ball}^G_r(C)/A)\bigr|\le t .$$
--   Then there is a $z$-definable flip $H$ of $G$ with $\mathrm{Ball}^H_{r+1}(C)\cap A=\emptyset$.
--
--   This is the step of the Closure Theorem that increases the separation radius by one.
--
--   **Formalization Note** $G$ is a graph on any vertex type, possibly infinite, and $C$ may be infinite.
--
--   Differences from the source:
--   - encoding: every graph (possibly infinite, Part I) → a SimpleGraph on any vertex type V : Type; reason: Part I allows infinite graphs
--   - encoding: z-definable flip G ⊕ (p̄, R) → an S-flip for some finite S with |S| ≤ z (IsSDefFlip); reason: the equivalent form printed on p.18
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Lemma 5.7, p.19 (PDF 21)

import Mathlib
import Definitions.Def_FOMCMonDep_tp
import Definitions.Def_FOMCMonDep_IsPFlip
import Definitions.Def_FOMCMonDep_VCDimLE

set_option autoImplicit false

namespace FOMCMonDep

/-- **Lemma 5.7.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §5.2, p.19 (PDF 21); proof §5.4: "For all d, t ∈ N, there is some z ∈ N
with the following property. For every graph G of VC-dimension at most d, radius r ∈ N, finite set A ⊆ V(G), and
arbitrary set C ⊆ V(G) satisfying Ball^G_r(C) ∩ A = ∅ and |ATypes^G(Ball^G_r(C)/A)| ⩽ t, there exists a z-definable
flip H of G in which Ball^H_{r+1}(C) ∩ A = ∅."

**Formalization Note.** Part I: `G` is a graph on any vertex type (possibly infinite), and `C` is arbitrary
(possibly infinite). `Ball_r(C)` is the union of the balls of the vertices of `C`. The type count is an `encard`. -/
theorem lemma_5_7 (d t : ℕ) :
    ∃ z : ℕ, ∀ (V : Type) (G : SimpleGraph V), VCDimLE G d → ∀ (r : ℕ) (A C : Set V), A.Finite →
      ballSet G r C ∩ A = ∅ → typeCount G.structure 1 0 (ballSet G r C) A ≤ t →
        ∃ H : SimpleGraph V, IsSDefFlip G z H ∧ ballSet H (r + 1) C ∩ A = ∅ := by sorry

end FOMCMonDep
