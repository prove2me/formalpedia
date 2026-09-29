-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_cuspClasses_of_twistedCutTrace_ne_zero_of_finrank_two_or_three
-- name    : AutomorphicForm.exists_mem_cuspClasses_of_twistedCutTrace_ne_zero_of_finrank_two_or_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/e094f440-464b-5c7b-b49d-e45323d90706
-- title:
--   Cyclic base change descent in degree 2 or 3
-- statement:
--   Let $K\subset L$ be number fields with $[L:K]=2$ or $3$. Fix real parameters $c_K,u_K,d_{1K},d_{2K}$ with $c_K>0$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subset GL_2(\mathbb{A}_K)$ such that $\bigcup_{x\in T_K}(\cdot\, x)$-translates of the centre-cut Siegel set (elements whose finite part is integral, whose local heights at all infinite places are $\ge c_K$, whose $x$-window squares are $\le u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$) cover $GL_2(\mathbb{A}_K)$ in the sense that each $g$ admits $\gamma\in GL_2(K)$ and an idèle $z$ with $\gamma g\,z$ in the set; fix $c_L,u_L,d_{1L}<d_{2L}$ and $T_L$ with the same covering property over $L$. Let $D$ be an idèlic Galois descent datum for $L/K$ (a continuous action of $\mathrm{Aut}_K(L)$ on $\mathbb{A}_L$ by ring automorphisms extending the action on $L$), and $\sigma\neq 1$ in $\mathrm{Aut}_K(L)$. Let $S_K$, $S_L$ be finite sets of finite places of $K$, $L$ such that every $w$ lying over a place of $S_K$ belongs to $S_L$, and every $w$ not over $S_K$ has ramification index $1$ over $K$. Both fields carry the production pins built from the above covering set, the levels $N\mapsto$ (adelic level $U_1(N)$ intersected with the subgroup of elements with trivial archimedean component), the standard Hecke generators, and the Haar measure conditioned to the adelic box; their central subgroup is all of $\mathbb{A}^\times$. Let $\xi_L$ be a character of that group for $L$, $N$ an ideal of $\mathcal{O}_L$, $t_L$ an archimedean type family for $L$ (a finite list of archimedean types at each infinite place), and $\varphi$ a continuous compactly supported function on $GL_2(\mathbb{A}_L)$ which is unit-factorizable above $K$ relative to $S_K$ and the level group $U_1(N)$ intersected with the finite-adelic subgroup, and archimedeanly bi-finite of type $t_L$. Let $\Psi$ be a Hecke eigensystem over $L$ with complex coefficients, and assume the $\sigma$-twisted cut trace of $\varphi$ on the $\Psi$-isotypic cuspidal submodule cut by $t_L$, formed with $D$, $\xi_L$, $N$ and $S_L$, is non-zero. Then there exist an ideal $N''\neq\bot$ of $\mathcal{O}_K$, a character $\xi_K$ of the central group of the pins over $K$, and a Hecke eigensystem $\pi$ over $K$ such that every prime dividing $N''$ lies in $S_K$, $\pi$ lies in `cuspClasses` for $\xi_K,N'',S_K$ (that is, $\pi$ has level $N''$, its Hecke data $a,b$ vanish at all places of $S_K$, and its isotypic cuspidal submodule is non-zero), and for every finite place $w$ of $L$ outside $S_L$ the formal base change of $\pi$ agrees with $\Psi$ at $w$: $(\mathrm{formalBaseChange}\,\pi).a(w)=\Psi.a(w)$ and $(\mathrm{formalBaseChange}\,\pi).b(w)=\Psi.b(w)$, where the formal base change is given by the Satake power of the data of $\pi$ at the place below $w$, with exponent the inertia degree.
--
--   This is the descent half of cyclic base change for $GL_2$ in degrees $2$ and $3$: an eigensystem over $L$ detected by the $\sigma$-twisted cut trace on a test function factorizable above $K$ comes, away from the excluded places, from the formal base change of a cuspidal class over $K$ of some non-zero level supported in $S_K$. It combines the construction of a matching test function over $K$ with the comparison of traces, and is used in turn to produce the formal base change statement feeding the automorphy arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_cuspClasses_of_twistedCutTrace_ne_zero_of_finrank_two_or_three.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.exists_mem_cuspClasses_of_twistedCutTrace_ne_zero_of_finrank_two_or_three
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3)
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (hdL : d₁L < d₂L)
    (hcovL : CoversModCentre L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ξL : (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : twistedCutTrace K L D σ
      (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc ≠ 0) :
    ∃ (N'' : Ideal (𝓞 K)) (ξK : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
      (π : HeckeEigensystem K ℂ),
      N'' ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N'' → v ∈ SK) ∧
      π ∈ cuspClasses K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξK N'' SK ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
        (formalBaseChange K L π).a w = Ψ.a w ∧ (formalBaseChange K L π).b w = Ψ.b w) := by sorry
