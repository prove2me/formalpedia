-- Prove2me | Theorems.Thm_AutomorphicForm_isLocallyConstant_and_hasCompactSupport_indicator_prod_semiLocalEval
-- name    : AutomorphicForm.isLocallyConstant_and_hasCompactSupport_indicator_prod_semiLocalEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/2c12cc29-4b87-5c2a-a4df-f516b3ce8813
-- title:
--   Local constancy and compact support of semi-local box functions
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $S_x$ be a finite set of height-one primes $v$ of $\mathcal{O}_K$, and for every height-one prime $v$ of $\mathcal{O}_K$ let $F_v \colon L \otimes_K K_v \to \mathbb{C}$ be a function, where $K_v$ denotes the adic completion of $K$ at $v$. Assume that for each $v \in S_x$ the function $F_v$ is locally constant and has compact support. For a height-one prime $v$ of $\mathcal{O}_K$ write $\mathrm{ev}_v \colon \mathbb{A}_{L,f} \to L \otimes_K K_v$ for the ring homomorphism [`AutomorphicForm.semiLocalEval K L v`](def/AutomorphicForm_TwistedOrbital.html#L441) on the finite adele ring of $L$, obtained by taking the components $x_w$ at the finitely many height-one primes $w$ of $\mathcal{O}_L$ lying under $v$ and transporting the resulting element of $\prod_{w \mid v} L_w$ back along the base-change isomorphism $L \otimes_K K_v \cong \prod_{w \mid v} L_w$, and let [`AutomorphicForm.semiLocalIntegers K L v`](def/AutomorphicForm_TwistedOrbital.html#L98) be the image of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_{K_v}$ in $L \otimes_K K_v$ under the canonical algebra map. The conclusion is that the function on $\mathbb{A}_{L,f}$ sending $x_f$ to $\prod_{v \in S_x} F_v(\mathrm{ev}_v(x_f))$ if $\mathrm{ev}_v(x_f)$ lies in [`AutomorphicForm.semiLocalIntegers K L v`](def/AutomorphicForm_TwistedOrbital.html#L98) for every $v \notin S_x$, and to $0$ otherwise, is both locally constant and compactly supported.
--
--   This is the standard statement that a 'box' function on the finite adeles of $L$ — prescribed locally constant compactly supported data at the finitely many places in $S_x$ and the integrality condition elsewhere — is locally constant with compact support, which is the finite-place half of membership in the Schwartz–Bruhat space. It is used in the analysis of twisted unipotent orbital integrals, being cited by [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram) and by [`AutomorphicForm.isOpen_and_isCompact_and_nonempty_and_exists_box_subset_of_forall_semiLocalEval_mem`](thm.html#AutomorphicForm.isOpen_and_isCompact_and_nonempty_and_exists_box_subset_of_forall_semiLocalEval_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isLocallyConstant_and_hasCompactSupport_indicator_prod_semiLocalEval.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicTracePushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.isLocallyConstant_and_hasCompactSupport_indicator_prod_semiLocalEval
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sx : Finset (HeightOneSpectrum (𝓞 K)))
    (Fv : (v : HeightOneSpectrum (𝓞 K)) → L ⊗[K] v.adicCompletion K → ℂ)
    (hFv : ∀ v ∈ Sx, IsLocallyConstant (Fv v) ∧ HasCompactSupport (Fv v)) :
    IsLocallyConstant (fun xf : FiniteAdeleRing (𝓞 L) L =>
        {xf : FiniteAdeleRing (𝓞 L) L | ∀ v ∉ Sx,
            AutomorphicForm.semiLocalEval K L v xf ∈ AutomorphicForm.semiLocalIntegers K L v}.indicator
          (fun xf => ∏ v ∈ Sx, Fv v (AutomorphicForm.semiLocalEval K L v xf)) xf) ∧
      HasCompactSupport (fun xf : FiniteAdeleRing (𝓞 L) L =>
        {xf : FiniteAdeleRing (𝓞 L) L | ∀ v ∉ Sx,
            AutomorphicForm.semiLocalEval K L v xf ∈ AutomorphicForm.semiLocalIntegers K L v}.indicator
          (fun xf => ∏ v ∈ Sx, Fv v (AutomorphicForm.semiLocalEval K L v xf)) xf) := by sorry
