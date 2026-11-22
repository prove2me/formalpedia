-- Prove2me | Theorems.Thm_AlpoGe_galoisLocalGlobal_geometry_witnesses
-- name    : AlpoGe.galoisLocalGlobal_geometry_witnesses
-- status  : Open
-- author  : @RSoulat
-- created : 2026-11-22T18:15:31.112314+00:00
-- url     : https://prove2.me/theorems/948cb575-3b35-4d86-9dc6-a808443039b5
-- title:
--   Alpöge’s Row0 Galois representations with local–global compatibility
-- statement:
--   For every CM number field $E$ and every regular algebraic polarized cuspidal representation of $\operatorname{GL}_a$ over $E$ with $a\ge1$, the existence statement UpperTheory.GalStar.Row0 holds for the local correspondence laws UpperTheory.Zero.LLC.IsRecT. For each coefficient prime and comparison isomorphism as quantified in Row0, the witnesses are a continuous semisimple Galois representation, an integral weight and Hodge–Tate multisets. They satisfy the weight relations, the compatibility conditions away from the coefficient prime and above it, and the crystalline clause for spherical local components. The tame comparison applies to every indicated place whose completion admits a continuous ring isomorphism with $\mathbb Q_p$ for some prime $p$.
--
--   This is the instance of galoisLocalGlobal_of_geometry_lift obtained by supplying the release’s geometric realization and theta-lifting theorems. It is the existence input to the release’s passage from Row0 to Row0b.
-- source:
--   L. Alpöge with Claude, 20 November 2026 Lean release. Specialize galoisLocalGlobal_of_geometry_lift (https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/Development.lean#L18-L31) to geoOne_holds (https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean#L11) and tLiftK (https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean#L4-L5).

import Definitions.Def_AlpoGeB008

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
  ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc
  Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst
  GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.GalStar UpperTheory.GalS

theorem AlpoGe.galoisLocalGlobal_geometry_witnesses :
  let rq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Prop :=
    ∃ (p : ℕ) (_ : Fact p.Prime) (iso : ℚ_[p] ≃+* w.adicCompletion E), Continuous iso
  let cmp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
      (x y : WD h) : Prop :=
    x.lpDim = y.lpDim ∧
    (Tor y → y.mono0 → x = y) ∧
    (rq w → TmW y → Sqf y → y.mono0 →
      x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g)
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
      (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ)
        (HT : (E →+* Qbar l) → Multiset ℤ),
        Continuous r ∧ IsSSRep r ∧
        (∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
            (A : ValuationSubring Ω) (h : IsPlaceOver A w)
            (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
            ∀ σ, π.IsLocComp w σ → cmp (wdOf h hl ι r) (rc (algNorm σ))) ∧
        (∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
          ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z)) ∧
        (∀ τ : E →+* Qbar l,
          HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)) ∧
        ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
          ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
            (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
            (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
            (∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ →
              IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
              IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
              ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
                IsInduced Bw τ τ' → IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)) ∧
            (∀ σ, π.IsLocComp w σ → ∀ rc, UpperTheory.Zero.LLC.IsRecT h rc →
              ((rq w ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ))) →
              (rc (algNorm σ)).mono0 →
              IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
              IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
              (∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
                IsInduced Bw τ τ' → IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)) ∧
              cmp (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))) := by sorry
