-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum
-- name    : AutomorphicForm.TwistedBruhat.finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/0552ca9d-3a5a-587a-a715-5524b55b1da0
-- title:
--   Unit-diagonal Bruhat fibres as sums over L
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $D$ be a Galois descent datum on the adeles of $L$ (a homomorphism $\tau \mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$, compatible with $L \to \mathbb{A}_L$ and continuous), let $\sigma$ be a $K$-automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ be arbitrary. Fix adeles $x, q$, ideles $t, \zeta$ and $k \in \mathrm{GL}_2(\mathbb{A}_L)$, write $n(\cdot)$ for $\begin{pmatrix}1&\ast\\0&1\end{pmatrix}$, $d(t) = \mathrm{diag}(t,1)$, $z(\zeta)$ for the central scalar matrix, $g = n(x)d(t)k$, and let $\sigma_D$ denote $D.\mathrm{act}\,\sigma$ applied entrywise (on ideles via the induced automorphism of the unit group). Two identities of $\mathbb{C}$-valued finsums (each equal to the corresponding sum when the summand has finite support, and to $0$ otherwise) are asserted. First, summing $\varphi\bigl(g^{-1}\,\delta\,\sigma_D(z(\zeta)g)\bigr)$ over those $\delta \in \mathrm{GL}_2(L)$ with $\delta_{10} = 0$, $\delta_{00} = \delta_{11} = 1$ that lie in $\mathrm{normUnipotentSet}$, i.e. for which some $\gamma \in \mathrm{GL}_2(K)$ of unipotent type has conjugacy class equal to the image of the $\sigma$-conjugacy class of $\delta$ under the twisted norm class map (here $\delta$ is pushed into $\mathrm{GL}_2(\mathbb{A}_L)$ entrywise), gives $$\sum_{b \in L,\ \mathrm{Tr}_{L/K}(b) \neq 0} \varphi\bigl(k^{-1} n\bigl((b + \sigma_D x - x)t^{-1}\bigr) d(\sigma_D t \cdot t^{-1}) z(\sigma_D \zeta)\, \sigma_D(k)\bigr).$$ Secondly, summing $\varphi\bigl(g^{-1}\,\delta\,\sigma_D(n(q)z(\zeta)g)\bigr)$ over all $\delta \in \mathrm{GL}_2(L)$ with $\delta_{10} = 0$ and $\delta_{00} = \delta_{11} = 1$ gives the analogous sum over all $b \in L$, with $b + \sigma_D q + (\sigma_D x - x)$ in place of $b + (\sigma_D x - x)$.
--
--   These are the contributions of the unit-diagonal fibres of the unipotent Bruhat cell to the $\sigma$-twisted kernel, written in Iwasawa coordinates: the geometric terms of type (ii) in the twisted trace formula for a cyclic extension, as in Langlands' treatment of base change for $\mathrm{GL}(2)$. The identity feeds the integration step [`AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub`](thm.html#AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub), where the inner sums over $L$ are compared with trace pushforwards.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum.lean

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicTracePushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward

theorem AutomorphicForm.TwistedBruhat.finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (x q : AdeleRing (𝓞 L) L) (t ζ : (AdeleRing (𝓞 L) L)ˣ) (k : AdelicGL2 (𝓞 L) L) :
    (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
        φ ((unipotentGL2 x * diagOne t * k)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * k))) =
      ∑ᶠ b ∈ {b : L | Algebra.trace K L b ≠ 0},
        φ (k⁻¹ *
          unipotentGL2 ((algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) *
            ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
          diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
          centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
          AutomorphicForm.sigmaAdelicAct K L D σ k)) ∧
    (∑ᶠ δ ∈ {δ : GL (Fin 2) L |
        (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
        φ ((unipotentGL2 x * diagOne t * k)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (unipotentGL2 q * (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * k)))) =
      ∑ᶠ b : L,
        φ (k⁻¹ *
          unipotentGL2 ((algebraMap L (AdeleRing (𝓞 L) L) b + D.act σ q + actSubId K L D σ x) *
            ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
          diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
          centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
          AutomorphicForm.sigmaAdelicAct K L D σ k)) := by sorry
