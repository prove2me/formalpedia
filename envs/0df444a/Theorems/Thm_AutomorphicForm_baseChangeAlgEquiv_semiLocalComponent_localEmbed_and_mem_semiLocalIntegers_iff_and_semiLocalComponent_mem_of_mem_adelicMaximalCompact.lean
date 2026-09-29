-- Prove2me | Theorems.Thm_AutomorphicForm_baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact
-- name    : AutomorphicForm.baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/dbf3379d-7231-596e-a6ef-d1ed757ac902
-- title:
--   Semi-local coordinates: local embedding, integrality, maximal compact
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $v$ be a height one prime of $\mathcal O_K$. Write $\mathrm{ev}_v$ for [`AutomorphicForm.semiLocalEval`](def/AutomorphicForm_TwistedOrbital.html#L441), the composite of the product of the evaluations at the primes $w$ of $\mathcal O_L$ lying over $v$ with the inverse of the base-change isomorphism $L\otimes_K K_v \xrightarrow{\sim} \prod_{w\mid v} L_w$, and `semiLocalComponent` for the induced map $GL_2(\mathbb A_{L,\mathrm f}) \to GL_2(L\otimes_K K_v)$. Three assertions are made. First, for every $w_0\mid v$, every $g\in GL_2(L_{w_0})$ and all $i,j\in\{0,1\}$, the $(i,j)$ entry of the semi-local component of $\iota_{w_0}(g)$ (the finite-adelic matrix with entries spliced from $g$ at $w_0$ and from the identity matrix elsewhere) has $w_0$-coordinate $g_{ij}$ and $w$-coordinate $\delta_{ij}$ for every $w\mid v$ with $w\neq w_0$. Second, $y\in L\otimes_K K_v$ lies in the image of $\mathcal O_L\otimes \mathcal O_v$ under `tensorAdicCompletionIntegersTo` if and only if every coordinate of its image in $\prod_{w\mid v}L_w$ lies in $\mathcal O_{L_w}$. Third, if $k\in GL_2(\mathbb A_L)$ has integral finite part and row-isometric archimedean components, then the semi-local component of its finite part and the inverse of that component both have all entries in the semi-local integers.
--
--   This is the basic dictionary for semi-local computations above a finite place $v$ of $K$ in the adelic theory of automorphic forms on $GL_2$: the identification $L\otimes_K K_v\cong\prod_{w\mid v}L_w$, the behaviour of a matrix placed at a single place above $v$, the coordinatewise criterion for semi-local integrality, and the integrality of the semi-local component of an element of the adelic maximal compact subgroup. It is used in the analysis of the unipotent term of the twisted trace formula and in the identification of its local factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    (∀ (w₀ : v.Extension (𝓞 L)) (g : GL (Fin 2) (w₀.1.adicCompletion L)) (i j : Fin 2),
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
          (((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 g) :
            GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) w₀ =
        (g : Matrix (Fin 2) (Fin 2) (w₀.1.adicCompletion L)) i j ∧
      ∀ w : v.Extension (𝓞 L), w ≠ w₀ →
        HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
            (((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 g) :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) w =
          (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j) ∧
    (∀ y : L ⊗[K] v.adicCompletion K,
      y ∈ AutomorphicForm.semiLocalIntegers K L v ↔
        ∀ w : v.Extension (𝓞 L),
          HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y w ∈ w.1.adicCompletionIntegers L) ∧
    (∀ k : AutomorphicForm.AdelicGL2 (𝓞 L) L, k ∈ AutomorphicForm.adelicMaximalCompact L →
      AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L k) ∈
        AutomorphicForm.semiLocalIntegralSet K L v) := by sorry
