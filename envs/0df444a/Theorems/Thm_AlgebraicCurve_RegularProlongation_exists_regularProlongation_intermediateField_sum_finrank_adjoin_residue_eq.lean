-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/449763cd-ff34-58a0-9cb3-2ce6f6eb895a
-- title:
--   Descent of a complete family of regular prolongations
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring with residue field $k$, and $F$ a field extension of $L$. For a finite index type $\iota$ let $\bar F_i$ be fields that are $k$-algebras, and let $R_i$ be regular prolongations of $A$ to $F$ with residue field $\bar F_i$: each $R_i$ consists of a valuation subring $\mathcal O_i$ of $F$, a ring homomorphism $\mathrm{res}_i \colon \mathcal O_i \to \bar F_i$ such that $x \in L$ satisfies $x \cdot 1 \in \mathcal O_i$ iff $x \in A$, $\mathrm{res}_i$ is surjective with kernel the maximal ideal of $\mathcal O_i$, $\mathrm{res}_i$ restricted to $A$ is the structure map $k \to \bar F_i$ composed with the residue map of $A$, and for every $g \neq 0$ in $F$ there is $c \in L$ with $c \cdot g \in \mathcal O_i$ and $\mathrm{res}_i(c\cdot g) \neq 0$. Let $f \in F$ lie in every $\mathcal O_i$, with each residue $\bar f_i = \mathrm{res}_i(f)$ transcendental over $k$ and $\sum_i [\bar F_i : k(\bar f_i)] = [F : L(f)]$. Let $L_1$ be an algebraically closed field with compatible maps into $L$ and $F$, and let $F_1$ be an $L_1$-intermediate field of $F$ containing $f$, with $F_1$ finite-dimensional over $L_1(f)$ and $[F_1 : L_1(f)] \le [F : L(f)]$. Assume moreover the descent data: for all $i \neq j$ some $u \in F_1$ lies in exactly one of $\mathcal O_i, \mathcal O_j$; and for each $i$ a family $b_l \in \mathcal O_i \cap F_1$ indexed by $\mathrm{Fin}\,[\bar F_i : k(\bar f_i)]$ whose residues $\mathrm{res}_i(b_l)$ are linearly independent over $k(\bar f_i)$. Then there exist fields $\bar F_{1,i}$ (in the universe of $F$), each an algebra over the residue field $k_1$ of $A_1 = A \cap L_1$ (the comap of $A$ along $L_1 \to L$), regular prolongations $R_{1,i}$ of $A_1$ to $F_1$ with residue fields $\bar F_{1,i}$, and ring homomorphisms $\varphi_i \colon \bar F_{1,i} \to \bar F_i$, together with the identification that for $u \in F_1$ one has $u \in (R_{1,i}).\mathrm{integers}$ iff $u \in \mathcal O_i$, such that: $i \mapsto (R_{1,i}).\mathrm{integers}$ is injective; $\varphi_i$ carries the residue of $u$ under $R_{1,i}$ to $\mathrm{res}_i(u)$; $\varphi_i$ is compatible with the structure maps $k_1 \to \bar F_{1,i}$ and $k \to \bar F_i$ along the residue maps of $A_1$ and $A$; $f$ is transcendental over $L_1$; each residue of $f$ under $R_{1,i}$ is transcendental over $k_1$; $\sum_i [\bar F_{1,i} : k_1(\text{residue of } f)] = [F_1 : L_1(f)]$; and $[F_1 : L_1(f)] = [F : L(f)]$.
--
--   This is the descent step in the theory of constant reductions of function fields: a complete family of regular prolongations of a valuation ring $A$ of $L$ to $F$ restricts to a complete family of regular prolongations of $A \cap L_1$ to a function subfield $F_1$ over an algebraically closed field of constants $L_1$, with the degree equality preserved, thereby reducing questions about valuation rings of arbitrary rank to those of finite rank. It is used in the proof that residues in the intersection of the residue spans are constants, over an algebraically closed constant field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq.{u}
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type u} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    {L₁ : Type*} [Field L₁] [IsAlgClosed L₁] [Algebra L₁ L] [Algebra L₁ F] [IsScalarTower L₁ L F]
    (F₁ : IntermediateField L₁ F) (hf₁ : f ∈ F₁)
    (hfd₁ : FiniteDimensional (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁)
    (hdeg : Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ ≤
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hsep : ∀ i j, i ≠ j → ∃ u ∈ F₁, ¬ (u ∈ (R i).integers ↔ u ∈ (R j).integers))
    (hbas : ∀ i, ∃ (b : Fin (Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)) → F) (hb : ∀ l, b l ∈ (R i).integers),
        (∀ l, b l ∈ F₁) ∧
        LinearIndependent (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
          (fun l => (R i).residue ⟨b l, hb l⟩)) :
    ∃ (Fb₁ : ι → Type u) (_ : ∀ i, Field (Fb₁ i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L))) (Fb₁ i))
      (R₁ : ∀ i, RegularProlongation (A.comap (algebraMap L₁ L)) F₁ (Fb₁ i))
      (φ : ∀ i, Fb₁ i →+* Fb i)
      (hO : ∀ i (u : F₁), u ∈ (R₁ i).integers ↔ (u : F) ∈ (R i).integers),
      Function.Injective (fun i => (R₁ i).integers) ∧
      (∀ i (u : F₁) (hu : (u : F) ∈ (R i).integers),
        φ i ((R₁ i).residue ⟨u, (hO i u).mpr hu⟩) = (R i).residue ⟨u, hu⟩) ∧
      (∀ i (a : A.comap (algebraMap L₁ L)),
        φ i (algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L))) (Fb₁ i)
          (IsLocalRing.residue _ a)) =
        algebraMap (IsLocalRing.ResidueField A) (Fb i)
          (IsLocalRing.residue A ⟨algebraMap L₁ L a, ValuationSubring.mem_comap.mp a.2⟩)) ∧
      Transcendental L₁ (⟨f, hf₁⟩ : F₁) ∧
      (∀ i, Transcendental (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L)))
        ((R₁ i).residue ⟨⟨f, hf₁⟩, (hO i _).mpr (hf i)⟩)) ∧
      ∑ i, Module.finrank (IntermediateField.adjoin
          (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L)))
          ({(R₁ i).residue ⟨⟨f, hf₁⟩, (hO i _).mpr (hf i)⟩} : Set (Fb₁ i))) (Fb₁ i)
        = Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ ∧
      Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ =
        Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by sorry
