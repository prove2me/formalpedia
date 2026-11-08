-- Prove2me | Theorems.Thm_BKAbsorption_minabs_properties
-- name    : BKAbsorption.minabs_properties
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T14:13:03.524977+00:00
-- url     : https://prove2.me/theorems/ace4957c-ff67-41e2-a2f9-d4a3b82b5568
-- title:
--   Minimal absorbing subuniverses and linked relations
-- statement:
--   $L$ is a signature without relation symbols. $A$ and $B$ are finite algebras in one Taylor variety: both are idempotent and satisfy the identities of one fixed Taylor term. $B\trianglelefteq A$ ($B$ absorbs $A$): $B$ is a subuniverse and some term operation $t$ gives $t(a_0,\dots,a_{n-1})\in B$ whenever all $a_i$ but at most one lie in $B$; proper means $\emptyset\neq B\neq A$; $B\trianglelefteq\!\!\trianglelefteq A$: $B$ is nonempty, absorbs $A$, and no proper subalgebra of $B$ absorbs $A$. $R\le_S A\times B$: $R$ is a subuniverse of $A\times B$ (coordinatewise operations) with both projections onto. $R$ is linked: any two elements of its first projection are joined by a chain whose consecutive elements have a common $R$-neighbour. Let $R\le_S A\times B$. (i) If $R$ is linked and $E\trianglelefteq R$ then $E$ is linked. (ii) If $C\trianglelefteq\!\!\trianglelefteq A$, $D\trianglelefteq\!\!\trianglelefteq B$ and $(C\times D)\cap R\neq\emptyset$, then $(C\times D)\cap R\le_S C\times D$. (iii) If moreover $R$ is linked, then $C\times D\subseteq R$ and $C\times D\trianglelefteq\!\!\trianglelefteq R$. (iv) If $R$ is linked and $C\trianglelefteq\!\!\trianglelefteq A$, there is $D\trianglelefteq\!\!\trianglelefteq B$ with $C\times D\subseteq R$. (v) If $R$ is linked, any two elements $c,d$ (each in $A$ or in $B$) lying in minimal absorbing subuniverses of $A$ or $B$ are joined by a path in the bipartite graph of $R$ all of whose vertices lie in minimal absorbing subuniverses of $A$ or $B$.
-- source:
--   L. Barto, M. Kozik, Absorbing subalgebras, cyclic terms, and the constraint satisfaction problem, Logical Methods in Computer Science 8(1:07) 2012, https://doi.org/10.2168/LMCS-8(1:7)2012 (arXiv:1201.0557), Prop 2.15

import Definitions.Def_BKAbsorption_defs

universe u v w w'

open FirstOrder FirstOrder.Language

namespace BKAbsorption

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Barto–Kozik, Proposition 2.15.  Let `A, B` be finite algebras in a Taylor variety (one Taylor
datum `T`) and `R ≤_S A × B`.
(i) If `R` is linked and `E ⊴ R`, then `E` is linked.
(ii) If `C ⊴⊴ A`, `D ⊴⊴ B` and `(C × D) ∩ R ≠ ∅`, then `(C × D) ∩ R ≤_S C × D` (its projections are `C` and `D`).
(iii) If `R` is linked, `C ⊴⊴ A`, `D ⊴⊴ B` and `(C × D) ∩ R ≠ ∅`, then `C × D ⊴⊴ R`
(in particular `C × D ⊆ R`).
(iv) If `R` is linked and `C ⊴⊴ A`, then there is `D ⊴⊴ B` with `C × D ⊆ R`.
(v) If `R` is linked and `c, d` (each in `A` or in `B`) lie in minimal absorbing subalgebras of
`A` or `B`, then `c` and `d` are linked via elements `c₀, …, c_j` each of which lies in some
minimal absorbing subalgebra of `A` or `B`. -/
theorem minabs_properties {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (R : L.Substructure (A × B)) (hsd : Subdirect (R : Set (A × B))) :
    (Linked (R : Set (A × B)) → ∀ E : Set R, IsAbsorbing L E →
        Linked (Subtype.val '' E : Set (A × B))) ∧
    (∀ (C : Set A) (D : Set B), MinAbsorbing L C → MinAbsorbing L D →
        (C ×ˢ D ∩ (R : Set (A × B))).Nonempty →
        Prod.fst '' (C ×ˢ D ∩ (R : Set (A × B))) = C ∧
          Prod.snd '' (C ×ˢ D ∩ (R : Set (A × B))) = D) ∧
    (Linked (R : Set (A × B)) → ∀ (C : Set A) (D : Set B), MinAbsorbing L C →
        MinAbsorbing L D → (C ×ˢ D ∩ (R : Set (A × B))).Nonempty →
        C ×ˢ D ⊆ (R : Set (A × B)) ∧ MinAbsorbing L {x : R | (x : A × B) ∈ C ×ˢ D}) ∧
    (Linked (R : Set (A × B)) → ∀ C : Set A, MinAbsorbing L C →
        ∃ D : Set B, MinAbsorbing L D ∧ C ×ˢ D ⊆ (R : Set (A × B))) ∧
    (Linked (R : Set (A × B)) → ∀ c d : A ⊕ B, InMinAbs L c → InMinAbs L d →
        Relation.ReflTransGen
          (fun x y => LinkAdj (R : Set (A × B)) x y ∧ InMinAbs L x ∧ InMinAbs L y) c d) := by sorry

end BKAbsorption
