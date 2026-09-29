-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_isSemiLocalFactorization_and_union_of_isArchTestFactor_of_isSemiLocalTestFn
-- name    : AutomorphicForm.exists_continuous_hasCompactSupport_isSemiLocalFactorization_and_union_of_isArchTestFactor_of_isSemiLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/c13c67af-d700-5df9-9531-b3ae288ed1c8
-- title:
--   Existence of semi-locally factorised test functions on GL₂(A_L)
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $S$ be a finite set of finite places of $K$, i.e. of height-one primes of $\mathcal{O}_K$. Let $\varphi_a : \mathrm{GL}_2(L_\infty) \to \mathbb{C}$ be an archimedean test factor: it has compact support and is of the form $g \mapsto \Phi(\mathrm{archEntries}(g))$ for some $C^\infty$ function $\Phi$ on the $2\times 2$ matrices over the mixed space of $L$, where $\mathrm{archEntries}$ sends $g$ to its matrix entries transported to the mixed space. Let $\varphi_S$ assign to each finite place $v$ of $K$ a function $\varphi_S(v)$ on $\mathrm{GL}_2(L \otimes_K K_v)$, and assume that for $v \in S$ each $\varphi_S(v)$ is locally constant with compact support. The conclusion produces $\varphi_0$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\varphi_{f,0}$ on $\mathrm{GL}_2(\mathbb{A}_L^f)$ such that $\varphi_0$ is continuous with compact support and $(\varphi_0,\varphi_{f,0})$ is a semi-local factorisation at $S$ with the given factors; that is: $\varphi_a$ is an archimedean test factor, $\varphi_{f,0}$ is locally constant with compact support, each $\varphi_S(v)$ for $v\in S$ is locally constant with compact support, $\varphi_{f,0}(h) = \prod_{v \in S} \varphi_S(v)(h^{(v)})$ whenever the semi-local component $h^{(v)}$ lies, for every $v \notin S$, in the set of $g \in \mathrm{GL}_2(L\otimes_K K_v)$ with both $g$ and $g^{-1}$ having entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_{K_v}$, $\varphi_{f,0}(h) = 0$ as soon as $h^{(v)}$ fails to be integral in this sense for some $v \notin S$, and $\varphi_0(g) = \varphi_a(g_\infty)\,\varphi_{f,0}(g_f)$ for all $g$. Moreover the same pair is a semi-local factorisation at $S \cup T$, for every finite set $T$ of finite places of $K$ disjoint from $S$, with the factor at $v \in T$ taken to be the indicator function of that integral set and the factor at $v \notin T$ unchanged.
--
--   This is the construction of the pure tensor test function $\varphi_a \otimes \bigotimes_{v \in S} \varphi_v \otimes \bigotimes_{v \notin S} \mathbf{1}_{\mathrm{GL}_2(\mathcal{O}_L \otimes \mathcal{O}_v)}$ on $\mathrm{GL}_2(\mathbb{A}_L)$, semi-locally factorised over the places of the base field $K$, together with the stability of the factorisation under enlarging $S$ by places where the factor is the integral indicator. It supplies the test functions used in the trace-formula and twisted-orbital-integral computations downstream, which invoke it to fix a factorisable $\varphi_0$ before comparing spectral and geometric expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_hasCompactSupport_isSemiLocalFactorization_and_union_of_isArchTestFactor_of_isSemiLocalTestFn.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_continuous_hasCompactSupport_isSemiLocalFactorization_and_union_of_isArchTestFactor_of_isSemiLocalTestFn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ S, IsSemiLocalTestFn K L v (φS v)) :
    ∃ (φ₀ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (φf₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      Continuous φ₀ ∧ HasCompactSupport φ₀ ∧ IsSemiLocalFactorization K L S φ₀ φa φf₀ φS ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint T S →
        IsSemiLocalFactorization K L (S ∪ T) φ₀ φa φf₀
          (fun v => if v ∈ T then (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) else φS v) := by sorry
