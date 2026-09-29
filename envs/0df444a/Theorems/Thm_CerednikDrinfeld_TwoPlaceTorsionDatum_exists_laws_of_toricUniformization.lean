-- Prove2me | Theorems.Thm_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization
-- name    : CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_toricUniformization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/bd08b63c-30ac-51a4-a790-05c158e4a885
-- title:
--   Two toric uniformisations give a two-place p-torsion datum
-- statement:
--   Fix a prime $p$, a natural number $M$ and primes $r_1,r_2$ with $p\neq r_1$ and $p\neq r_2$. Let $D_1$ be degeneracy data on finite types $E_1,V_1$ (two maps $a,b\colon E_1\to V_1$ and weights $w\colon E_1\to\mathbb{N}^{+}$) with Hecke data $H_1$, and likewise $D_2,H_2$ on $E_2,V_2$; let $A_1,A_2$ be valuation subrings of $\overline{\mathbb{Q}}=\mathrm{AlgebraicClosure}\ \mathbb{Q}$ with $r_1$, respectively $r_2$, a non-unit of them. Let $T$ be an abelian group carrying a ring homomorphism `hecke` from $\mathbb{T}=\mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbb{Z}$ to $\mathrm{End}_{\mathbb{Z}}T$ and a monoid homomorphism `gal` from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to the additive automorphisms of $T$, the two actions commuting, such that: (i) some finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ has the property that every $\sigma$ fixing $L$ pointwise acts trivially on $\{t : p\cdot t=0\}$; (ii) for every prime $\ell\nmid M$, every valuation subring $B$ over $\ell$ and every $\sigma$ in the inertia subgroup of $B$ over $\mathbb{Q}$, $\sigma$ acts trivially on that $p$-torsion; (iii) for such $\ell,B$ and every $\sigma$ lying in the decomposition group and inducing $x\mapsto x^{\ell}$ on the residue field of $B$, one has $\sigma^{2}t-T_{\ell}(\sigma t)+\ell\, t=0$ for all $t$ with $p\cdot t=0$, where $T_\ell$ denotes the image of the generator `heckeGen` at $\ell$. Assume finally two toric uniformisations of $(T,\mathrm{hecke},\mathrm{gal})$: terms $\mathcal{U}_1$ of `ToricUniformization p r₁ D₁ H₁ A₁ hA₁ …` and $\mathcal{U}_2$ of the corresponding type for $r_2,D_2,H_2,A_2$; each consists of a divisible abelian group $U$ with Hecke action, a homomorphism $\pi\colon U\to T$ hitting all of the $p$-torsion and commuting with Hecke, an identification of $\ker\pi$ with the ribbon kernel $Y=\bigcap_i\ker(\mathrm{jointDelta}\,D\,i)\subseteq(E\to\mathbb{Z})$ adjoint to the Hecke action with respect to the ribbon Gram pairing, an identification of $U[p]$ with $\mathrm{Hom}_{\mathbb{Z}}(Y,\mathbb{Z}/p)$ compatible with Hecke operators, a surjective tame character from the inertia subgroup at $A$ onto $\mathbb{Z}/p$, and a Kummer law relating $\sigma\pi(u)-\pi(u)$ to the reduction mod $p$ of the Gram pairing. Then there exists a two-place $p$-torsion datum $\mathcal{J}$ of type `TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂` — that is, a finite abelian group killed by $p$ with commuting Hecke and Galois actions of finite level, two distinguished subgroups identified with $\mathrm{Hom}_{\mathbb{Z}}(Y_i,\mathbb{Z}/p)$ and specialisation homomorphisms from the inertia invariants at $A_i$ to the ribbon component group $\mathrm{Hom}_{\mathbb{Z}}(Y_i,\mathbb{Z})/\mathrm{ran}(\mathrm{ribbonGram}\,D_i)$ — which satisfies `𝒥.Laws M r₁ r₂`: the one-place datum `𝒥.fst` has good reduction outside $M$ and satisfies the local laws at $r_1$, and `𝒥.snd` satisfies the local laws at $r_2$.
--
--   This is the purely toric case of Grothendieck's description of the $p$-torsion of a semistable abelian variety over a local field of residue characteristic different from $p$, packaged so that the character groups and monodromy pairings of the two places of bad reduction are recorded simultaneously; it converts two $r_i$-adic uniformisation presentations of one Galois–Hecke module into the combinatorial datum on which the level-lowering argument operates. It is used in the construction of such a datum from the Čerednik–Drinfeld class-set description, in [`CerednikDrinfeld.exists_twoPlaceTorsionDatum_laws_classSet_of_squarefree_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_twoPlaceTorsionDatum_laws_classSet_of_squarefree_of_six_mul_dvd_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.lean

import Definitions.Def_CerednikDrinfeld_ToricUniformization
import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CerednikDrinfeld

theorem CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_toricUniformization
    {p : ℕ} [Fact p.Prime] {M r₁ r₂ : ℕ} [Fact r₁.Prime] [Fact r₂.Prime] (hpr₁ : p ≠ r₁) (hpr₂ : p ≠ r₂)
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)} (hA₁ : A₁.LiesOverPrime r₁) (hA₂ : A₂.LiesOverPrime r₂)
    (T : Type) [AddCommGroup T] (hecke : HeckeAlg →+* Module.End ℤ T)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T)
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → ∀ t : T, p • t = 0 → gal σ t = t)
    (unramified : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ t : T, p • t = 0 → gal σ t = t)
    (eichlerShimura : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt σ ℓ →
          ∀ t : T, p • t = 0 → gal σ (gal σ t) - hecke (heckeGen ⟨ℓ, hℓ⟩) (gal σ t) + ℓ • t = 0)
    (𝒰₁ : ToricUniformization p r₁ D₁ H₁ A₁ hA₁ T hecke gal) (𝒰₂ : ToricUniformization p r₂ D₂ H₂ A₂ hA₂ T hecke gal) :
    ∃ 𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂, 𝒥.Laws M r₁ r₂ := by sorry
