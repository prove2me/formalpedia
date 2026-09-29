-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isUnitFactorization_insert_and_cutTrace_eq_pow_mul_cutTrace
-- name    : AutomorphicForm.exists_isUnitFactorization_insert_and_cutTrace_eq_pow_mul_cutTrace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/c758e762-c653-5750-9085-d9ab13c049fa
-- title:
--   Hecke and central translates of a factorizable test function
-- statement:
--   Let $K$ be a number field, $W$ a set of elements of $\mathrm{GL}_2(\mathbb{A}_K)$, $\mathrm{tys}_K$ an archimedean type family (a number of types at each infinite place together with representations of the relevant isometry subgroups), $N'$ an ideal of $\mathcal{O}_K$, $S_K$ and $S'$ finite sets of finite places, and $\xi_K$ a homomorphism from the full subgroup of the idele units to $\mathbb{C}^\times$. Let $f\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous with compact support, equipped with data $f_a$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$, $f_f$ on $\mathrm{GL}_2(\mathbb{A}_K^{\mathrm{fin}})$ and local factors $f_S(u)$ on each $\mathrm{GL}_2(K_u)$ forming a unit factorization relative to $S'$: $f_a$ is the restriction of a smooth function of the archimedean matrix entries and has compact support, $f_f$ is locally constant with compact support, each $f_S(u)$ for $u\in S'$ is locally constant with compact support, $f_f(h)=\prod_{u\in S'}f_S(u)(h_u)$ whenever $h_u$ lies in the set of matrices with $h_u$ and $h_u^{-1}$ integral for all $u\notin S'$, $f_f(h)=0$ when this fails at some $u\notin S'$, and $f(g)=f_a(g_\infty)f_f(g_{\mathrm{fin}})$. Assume further that $f$ is invariant under left and right translation by $\mathrm{principalLevel}(N')\cap\ker(\mathrm{glArch})$, and that $f$ is archimedean bi-finite of type $\mathrm{tys}_K$, that is $g\mapsto f(g^{-1})$ lies in the archimedean cut submodule and $f$ in the archimedean dual cut submodule of that type. Let $v$ be a finite place with $v\notin S'$, $v\notin S_K$ and $v\nmid N'$, let $\varpi_K\in\mathcal{O}_v$ be irreducible with nonzero image in $K_v$, let $rT\colon \mathrm{Fin}\,n\to \mathrm{GL}_2(K_v)$ be a system of representatives for the left cosets in the double coset of $\mathrm{diag}(\varpi_K,1)$ modulo the image of $\mathrm{GL}_2(\mathcal{O}_v)$ (each representative in the double coset, every element of it congruent to one, and the induced map to the quotient injective), let $z\in\mathrm{GL}_2(K_v)$ be the scalar matrix $\varpi_K\cdot 1$, and let $k,j$ be natural numbers. Then there exist a continuous compactly supported $f''\colon\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and a function $f''_f$ on $\mathrm{GL}_2(\mathbb{A}_K^{\mathrm{fin}})$ such that $f''$ has a unit factorization relative to $\mathrm{insert}\,v\,S'$ with archimedean factor the same $f_a$, finite factor $f''_f$, and local factors $f_S$ modified at $v$ to $x\mapsto\sum_{\iota\colon\mathrm{Fin}\,k\to\mathrm{Fin}\,n}\mathbf{1}\bigl[(rT(\iota(0))\cdots rT(\iota(k-1))\,z^{j})^{-1}x \text{ integral with integral inverse}\bigr]$; moreover $f''$ is bi-invariant under the same level subgroup, is archimedean bi-finite of type $\mathrm{tys}_K$, and for every Hecke eigensystem $\pi$ over $\mathbb{C}$ one has $\mathrm{cutTrace}(f'')=\pi.a(v)^{k}\,\bigl(\mathrm{Nm}(v)^{-1}\pi.b(v)\bigr)^{j}\,\mathrm{cutTrace}(f)$, both cut traces being taken with the carrier pins given by $W$, the level family $M\mapsto\mathrm{principalLevel}(M)\cap\ker(\mathrm{glArch})$, the Hecke generators $u\mapsto\mathrm{heckeGen}(u)$ and the adelic box, with $\xi_K$, $N'$, $S_K$, $\pi$ and $\mathrm{tys}_K$; here $\mathrm{Nm}(v)$ is the absolute norm of the prime ideal of $v$.
--
--   This is the statement that, on the isotypic cuspidal space attached to a Hecke eigensystem $\pi$, the unramified Hecke operator at a good place $v$ and the central element $\varpi_v\cdot 1$ act through the scalars $\pi.a(v)$ and $\mathrm{Nm}(v)^{-1}\pi.b(v)$, expressed as a scalar law for the cut traces of Hecke and central translates of a factorizable test function. It is used by the downstream comparisons of Hecke word sums with twisted cut traces and by the computation of fibre sums for central elliptic elements at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isUnitFactorization_insert_and_cutTrace_eq_pow_mul_cutTrace.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_LocalLanglands_HeckeCosetLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isUnitFactorization_insert_and_cutTrace_eq_pow_mul_cutTrace
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (W : Set (AdelicGL2 (𝓞 K) K)) (tysK : ArchTypeFamily K)
    (N' : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S' : Finset (HeightOneSpectrum (𝓞 K)))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ u : HeightOneSpectrum (𝓞 K), GL (Fin 2) (u.adicCompletion K) → ℂ)
    (hfact : IsUnitFactorization K S' f fa ff fS)
    (hbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) f)
    (harch : IsArchBiFinite K tysK f)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S') (hvS : v ∉ SK) (hvN : ¬ v.asIdeal ∣ N')
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    {n : ℕ} (rT : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rT)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ) :
    ∃ (f'' : AdelicGL2 (𝓞 K) K → ℂ) (hf'' : Continuous f'') (hf''c : HasCompactSupport f'')
      (ff'' : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsUnitFactorization K (insert v S') f'' fa ff''
          (Function.update fS v fun x => ∑ ι : Fin k → Fin n,
            (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
              (((List.ofFn fun m => rT (ι m)).prod * z ^ j)⁻¹ * x)) ∧
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) f'' ∧
        IsArchBiFinite K tysK f'' ∧
        ∀ π : HeckeEigensystem K ℂ,
          cutTrace K
              (productionPinsOf K W (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π tysK f'' hf'' hf''c =
            π.a v ^ k * π.toRawCentral.b v ^ j *
              cutTrace K
                (productionPinsOf K W
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π tysK f hf hfc := by sorry
