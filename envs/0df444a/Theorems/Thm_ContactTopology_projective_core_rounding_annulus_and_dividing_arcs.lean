-- Prove2me | Theorems.Thm_ContactTopology_projective_core_rounding_annulus_and_dividing_arcs
-- name    : ContactTopology.projective_core_rounding_annulus_and_dividing_arcs
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T02:03:44.480466+00:00
-- url     : https://prove2.me/theorems/ddf356c3-11aa-4e2b-a129-ab22d8119cb4
-- title:
--   The actual rounded Legendrian-core annulus in projective space and its two dividing arcs
-- statement:
--   Let $F$ be an antipodally equivariant coorientation-preserving contactomorphism of the standard contact three-sphere, and let $r>0$. Construct the actual smooth convex rounding in its twice-rotating Legendrian-core collar, and prove that it gives an embedded annulus both upstairs and in real projective three-space.
--
--   The construction includes a smooth sphere-valued collar $C$, a positive contact factor $L$, a smooth surface $S$, an actual transverse contact vector field $Y$ on an open sphere neighborhood, a smooth phase $\psi$, and smooth regular lifted dividing branches. The collar has
--   $$C^*\lambda=L\bigl(\sin(4\pi z)\,dx+\cos(4\pi z)\,dy\bigr),\qquad
--   C(0,0,z)=F(\cos(2\pi z),\sin(2\pi z),0,0).$$
--   The rounding agrees to all orders with the original flat collar faces outside its bend, has exact integer longitudinal fibers, and satisfies $S(s,z+1/2)=-S(s,z)$. Its longitudinal rulings, including the boundary circles, are Legendrian. The field is smooth and tangent to the sphere, odd on the stated neighborhood, satisfies the contact Lie-derivative identity, and is transverse everywhere along the surface. All these data are constructed from the actual supplied map, with no input field or annulus certificate.
--
--   In addition, there are topological embeddings
--   $$E:[0,1]\times(\mathbb R/\mathbb Z)\hookrightarrow S^3,\qquad
--   P:[0,1]\times\bigl(\mathbb R/(\tfrac12\mathbb Z)\bigr)\hookrightarrow\mathbb{RP}^3.$$
--   The first is induced by the same lifted surface, and the second is exactly its antipodal projection. Their images are exactly the compact rounded annulus and its projection, respectively. A sphere-valued lift identifies these maps pointwise, so the embeddings are not unrelated witnesses.
--
--   The projective dividing locus consists of exactly two disjoint embedded arcs. They are the projections of
--   $$z=-\frac{\psi(s)}{4\pi},\qquad
--   z=\frac14-\frac{\psi(s)}{4\pi},\qquad 0\le s\le1,$$
--   where $\psi(0)=0$ and $\psi(1)=\pi/2$. The statement includes an exact equivalence between the vanishing of $\lambda(Y)$ on the lifted annulus and membership in these two projective branches. All lifted branches connect $C(0,rc,k/4)$ to $C(rc,0,k/4-1/8)$; after the half-period identification, the four branches upstairs yield precisely these two arcs downstairs.
--
--   This is an explicit sphere-core and projective-core instance of the local edge-rounding construction in Honda. The quotient embeddings and projected arcs are asserted in the topological sense, with globally smooth immersed sphere lifts and an actual equivariant transverse contact-field lift. A quotient tangent-bundle formalization, general edge gluing, bypass existence, generic convex movies, and the core-isotopy classification remain separate obligations.
-- source:
--   Ko Honda, Gluing tight contact structures, https://arxiv.org/pdf/math/0102029, Section 1.5, p.11, rotating collar edge rounding and -1/(4n) dividing shift; Section 1.1 p.2 convexity. Derived explicit n=2 construction and antipodal quotient for an actual equivariant sphere contactomorphism. The quotient and two-arc conclusions follow from exact period and antipodal fibers; not the arbitrary-manifold gluing theorem. Context: Hyunki Min, https://arxiv.org/html/2207.03590v2, Proposition 3.5 and Section 4, projective lens-space specialization.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Definitions.Def_ContactTopology_AntipodalSphereQuotients
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Order.IntermediateValue
open BirkhoffGlobalSection ContactTopology.Projective Set Function Filter
open scoped ContDiff Topology

theorem ContactTopology.projective_core_rounding_annulus_and_dividing_arcs
    (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, ∃ C : (Fin 3 → ℝ) → Phase, ∃ L : (Fin 3 → ℝ) → ℝ,
    ∃ S : ℝ × ℝ → Phase, ∃ Y : Phase → Phase, ∃ O : Set Phase,
    ∃ phase : ℝ → ℝ, ∃ γ : ℤ → ℝ → Phase,
      0 < c ∧ ContDiff ℝ ∞ C ∧ ContDiff ℝ ∞ L ∧ (∀ y, 0 < L y) ∧
      (∀ y, C y ∈ unitThreeSphere) ∧ (∀ y, Injective (fderiv ℝ C y)) ∧
      (∀ z, C ![0,0,z]=F.toFun ![Real.cos (2*Real.pi*z),Real.sin (2*Real.pi*z),0,0]) ∧
      (∀ y v, phaseRadialContact (C y) (fderiv ℝ C y v)=
        L y*(Real.sin (4*Real.pi*y 2)*v 0+Real.cos (4*Real.pi*y 2)*v 1)) ∧
      ContDiff ℝ ∞ S ∧ (∀ p, S p ∈ unitThreeSphere) ∧
      (∀ p, Injective (fderiv ℝ S p)) ∧
      (∀ p q, S p=S q ↔ p.1=q.1 ∧ ∃ k : ℤ, p.2=q.2+k) ∧
      (∀ s z, S (s,z+1/2)= -S (s,z)) ∧
      (∀ s z, s ≤ 0 → S (s,z)=C ![0,r*(c-s),z]) ∧
      (∀ s z, 1 ≤ s → S (s,z)=C ![r*(c+s-1),0,z]) ∧
      IsCompact (S '' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) ∧
      (∀ y, y ∈ S '' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ↔
        ∃ s ∈ Icc (0:ℝ) 1, ∃ z : ℝ, y=S (s,z)) ∧
      IsOpen O ∧ range S ⊆ O ∧
      (∀ y ∈ O ∩ unitThreeSphere, ContDiffAt ℝ ∞ Y y ∧ phaseDot y (Y y)=0 ∧
        Y (-y)= -Y y ∧ ∃ a : ℝ, ∀ w : Phase, phaseDot y w=0 →
          phaseRadialContact (Y y) w+phaseRadialContact y (fderiv ℝ Y y w)=a*phaseRadialContact y w) ∧
      (∀ p v : ℝ × ℝ, Y (S p) ≠ fderiv ℝ S p v) ∧
      (∀ p : ℝ × ℝ, phaseRadialContact (S p) (fderiv ℝ S p (0,1))=0) ∧
      ContDiff ℝ ∞ phase ∧ phase 0=0 ∧ phase 1=Real.pi/2 ∧
      (∀ k, ContDiff ℝ ∞ (γ k)) ∧
      (∀ k s, γ k s=S (s,(k:ℝ)/4-phase s/(4*Real.pi))) ∧
      (∀ k s, deriv (γ k) s ≠ 0) ∧
      (∀ k, γ k 0=C ![0,r*c,(k:ℝ)/4] ∧ γ k 1=C ![r*c,0,(k:ℝ)/4-1/8]) ∧
      (∀ s ∈ Icc (0:ℝ) 1, ∀ z : ℝ,
        (phaseRadialContact (S (s,z)) (Y (S (s,z)))=0 ↔
          ∃ k : ℤ, z=(k:ℝ)/4-phase s/(4*Real.pi))) ∧
      ∃ T : ℝ × ℝ → RoundSphere 4, (∀ p, (T p).val=S p) ∧
      ∃ E : Icc (0:ℝ) 1 × AddCircle (1:ℝ) → Phase,
      ∃ P : Icc (0:ℝ) 1 × AddCircle (1/2:ℝ) → ProjectiveSphere 4,
      ∃ Γ₀ Γ₁ : Icc (0:ℝ) 1 → ProjectiveSphere 4,
        Topology.IsEmbedding E ∧ Topology.IsEmbedding P ∧
        (∀ s, ∀ z : ℝ, E (s,(z:AddCircle (1:ℝ)))=S (s.val,z)) ∧
        (∀ s, ∀ z : ℝ, P (s,(z:AddCircle (1/2:ℝ)))=project 4 (T (s.val,z))) ∧
        range E=S '' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ∧
        range P=project 4 '' {y : RoundSphere 4 | y.val ∈ range E} ∧
        Topology.IsEmbedding Γ₀ ∧ Topology.IsEmbedding Γ₁ ∧
        Disjoint (range Γ₀) (range Γ₁) ∧
        (∀ s, Γ₀ s=P (s,((-phase s.val/(4*Real.pi):ℝ):AddCircle (1/2:ℝ)))) ∧
        (∀ s, Γ₁ s=P (s,((1/4-phase s.val/(4*Real.pi):ℝ):AddCircle (1/2:ℝ)))) ∧
        ∀ s : Icc (0:ℝ) 1, ∀ z : ℝ,
          phaseRadialContact (S (s.val,z)) (Y (S (s.val,z)))=0 ↔
            project 4 (T (s.val,z))=Γ₀ s ∨ project 4 (T (s.val,z))=Γ₁ s := by sorry
