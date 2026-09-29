-- Prove2me | Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_mul_ideleNorm_det_rpow_principalLevel_and_levelOne_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.isIsotypicCuspFormAt_mul_ideleNorm_det_rpow_principalLevel_and_levelOne_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/0c8763ab-0f0e-57b5-9bd9-073f9e7ca493
-- title:
--   Twisting isotypic cusp forms by ‖det‖^{w/2} between levels U₁(N) and U(N)
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta\in\mathbb R$ with $0<\alpha$, and let $\Phi_1,\Phi_2\subseteq\mathrm{GL}_2(\mathbb A_K)$ both be contained in the determinant slab $\{g:\ \|\det g\|\in[\alpha,\beta]\}$, where $\|\cdot\|$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the module of the idele acting on the adeles, and let each of $\Phi_1,\Phi_2$ be a fundamental domain for the image of $\mathrm{GL}_2(K)$ under `globalPoints` (the entrywise map induced by $K\to\mathbb A_K$) acting on the adelic Haar measure `adelicGLHaar` restricted to that slab. Let $\xi,\xi'$ be homomorphisms from the full subgroup of $\mathbb A_K^\times$ to $\mathbb C^\times$ and $w\in\mathbb R$ with $\xi'(z)\,\|z\|^{w}=\xi(z)$ for all $z\in\mathbb A_K^\times$; let $N$ be an ideal of $\mathcal O_K$ and $S$ a finite set of finite places containing every $v$ whose prime divides $N$. Two sets of pins are formed by `productionPinsOf`, both with measure `adelicGLHaar`, central subgroup $\top$, Hecke generators `heckeGen` at each $v$, and the conditional additive Haar measure on the box `adelicBox`: one at $\Phi_1$ with level family $M\mapsto$ `levelOne` $M\ \sqcap$ `finiteAdelicGL2Subgroup`, the other at $\Phi_2$ with $M\mapsto$ `principalLevel` $M\ \sqcap$ `finiteAdelicGL2Subgroup`. Here `IsIsotypicCuspFormAt` at given pins for $(\xi,N,S,\Psi)$ means: $\varphi$ is a smooth cusp automorphic function for $\xi$ at those pins, $\varphi$ is continuous, $\varphi$ is right invariant under the level group at $N$, for every $v\notin S$ it is a Hecke coset eigenfunction at `heckeGen` $v$ with eigenvalue $\Psi.a\,v$, and for every $v\notin S$ it satisfies $\varphi(\mathrm{diag}(\det(\mathtt{heckeGen}\,v))\,g)=(\mathtt{cNorm}\,v)^{-1}\Psi.b\,v\cdot\varphi(g)$. The conclusion is a conjunction of two transfers. First, for every Hecke eigensystem $\Psi$ over $\mathbb C$ and every $u:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$: if $u$ is isotypic for $(\xi,N,S,\Psi)$ at the $\Phi_1$/`levelOne` pins, then $g\mapsto u(g)\,\|\det g\|^{-w/2}$ is isotypic for $(\xi',N,S)$ at the $\Phi_2$/`principalLevel` pins with eigensystem $\Psi$ twisted by $v\mapsto q_v^{w/2}$, i.e. $a_v\mapsto q_v^{w/2}a_v$, $b_v\mapsto q_v^{w}b_v$ and the same level, $q_v$ being the absolute norm of $v$. Second, conversely: if $u$ is isotypic for $(\xi',N,S,\Psi)$ at the $\Phi_2$/`principalLevel` pins and, in addition, $u$ is right invariant under `levelOne` $N\ \sqcap$ `finiteAdelicGL2Subgroup` (an extra hypothesis, not implied by invariance at principal level), then $g\mapsto u(g)\,\|\det g\|^{w/2}$ is isotypic for $(\xi,N,S)$ at the $\Phi_1$/`levelOne` pins with $\Psi$ twisted by $v\mapsto q_v^{-w/2}$.
--
--   This is the standard device of twisting an automorphic form on $\mathrm{GL}_2$ by a real power of $\|\det\|$, which shifts the central character by $\|\cdot\|^{w}$ and rescales the unramified Hecke data by powers of $q_v$; here it is combined with a change of the fundamental domain inside the determinant slab and with the passage between the level families $U_1(M)$ and $U(M)$. It is used in the comparison of twisted cut traces at principal level with those at level $U_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isIsotypicCuspFormAt_mul_ideleNorm_det_rpow_principalLevel_and_levelOne_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isIsotypicCuspFormAt_mul_ideleNorm_det_rpow_principalLevel_and_levelOne_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α)
    (Φ₁ Φ₂ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₁s : Φ₁ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₁ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₁
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₂s : Φ₂ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₂ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₂
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ ξ' : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (w : ℝ)
    (hξ' : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (((NumberField.TateGlobal.ideleNorm K z) ^ w : ℝ) : ℂ) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S) :
    (∀ (Ψ : HeckeEigensystem K ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ),
      IsIsotypicCuspFormAt K
        (productionPinsOf K Φ₁ (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ u →
      IsIsotypicCuspFormAt K
        (productionPinsOf K Φ₂ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ' N S
        (Ψ.twist fun v => ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (w / 2) : ℝ) : ℂ))
        (fun g => u g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ))) ∧
    (∀ (Ψ : HeckeEigensystem K ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ),
      IsIsotypicCuspFormAt K
        (productionPinsOf K Φ₂ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ' N S Ψ u →
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        u (g * k) = u g) →
      IsIsotypicCuspFormAt K
        (productionPinsOf K Φ₁ (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S
        (Ψ.twist fun v => ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(w / 2)) : ℝ) : ℂ))
        (fun g => u g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ))) := by sorry
