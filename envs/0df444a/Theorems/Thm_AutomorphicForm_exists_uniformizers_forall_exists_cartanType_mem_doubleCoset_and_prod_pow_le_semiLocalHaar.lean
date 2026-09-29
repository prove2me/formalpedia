-- Prove2me | Theorems.Thm_AutomorphicForm_exists_uniformizers_forall_exists_cartanType_mem_doubleCoset_and_prod_pow_le_semiLocalHaar
-- name    : AutomorphicForm.exists_uniformizers_forall_exists_cartanType_mem_doubleCoset_and_prod_pow_le_semiLocalHaar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/0193f224-983e-594b-ba49-5e93d98dda2b
-- title:
--   Semi-local Cartan type and volume bound for KaK
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, let $v$ be a nonzero prime of $\mathcal{O}_K$, and assume the set $v.\mathrm{Extension}\,(\mathcal{O}_L)$ of primes $w$ of $\mathcal{O}_L$ lying under $v$ is finite. Write $\mathcal{K}$ for [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136), the set of $g \in \mathrm{GL}_2(L \otimes_K K_v)$ such that both $g$ and $g^{-1}$ have all entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_v$ in $L \otimes_K K_v$, and $\mathcal{K}_w$ for the analogous set [`AutomorphicForm.localIntegralSet L w`](def/AutomorphicForm_LocalOrbitalBase.html#L100) inside $\mathrm{GL}_2(L_w)$; let $\mu$ be [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169), the Haar measure on $\mathrm{GL}_2(L \otimes_K K_v)$ (for the Borel structure of its topology) normalised so that $\mu(\mathcal{K}) = 1$. The assertion is that there is a family of elements $\pi_w \in L_w$, one for each $w \mid v$, with $\pi_w \neq 0$ and $\|\pi_w\| = (\mathrm{absNorm}\,w)^{-1}$, such that for every $a \in \mathrm{GL}_2(L \otimes_K K_v)$ there are integers $k_w$, natural numbers $m_w$, and elements $d_w \in \mathrm{GL}_2(L_w)$ whose matrices are $\mathrm{diag}(\pi_w^{k_w + m_w}, \pi_w^{k_w})$, for which: every $g \in \mathcal{K}\{a\}\mathcal{K}$ has, at each $w \mid v$, its image under the $w$-th component of the base change isomorphism $L \otimes_K K_v \cong \prod_{w \mid v} L_w$ applied entrywise to $\mathrm{GL}_2$ lying in $\mathcal{K}_w \{d_w\} \mathcal{K}_w$; moreover $\prod_{w \mid v} (\mathrm{absNorm}\,w)^{m_w} \le \mu(\mathcal{K}\{a\}\mathcal{K})$ as real numbers, and $\mu(\mathcal{K}\{a\}\mathcal{K}) \neq \infty$.
--
--   This is the Cartan (elementary divisor) decomposition of $a$ place by place above $v$, recorded together with the resulting lower bound for the volume of the double coset $\mathcal{K}a\mathcal{K}$ in the Haar measure normalised by $\mu(\mathcal{K})=1$. It is used in bounding integrals of a density over the sets of upper triangular elements of double cosets, in the analytic estimates entering the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_uniformizers_forall_exists_cartanType_mem_doubleCoset_and_prod_pow_le_semiLocalHaar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_uniformizers_forall_exists_cartanType_mem_doubleCoset_and_prod_pow_le_semiLocalHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))] :
    ∃ π : ∀ w : v.Extension (𝓞 L), w.1.adicCompletion L,
      (∀ w, π w ≠ 0 ∧ ‖π w‖ = ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)⁻¹) ∧
      ∀ a : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        ∃ (k : v.Extension (𝓞 L) → ℤ) (m : v.Extension (𝓞 L) → ℕ)
          (d : ∀ w : v.Extension (𝓞 L), GL (Fin 2) (w.1.adicCompletion L)),
          (∀ w, ((d w : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
              Matrix.diagonal ![π w ^ (k w + m w), π w ^ (k w)]) ∧
          (∀ g ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v,
            ∀ w : v.Extension (𝓞 L),
              Matrix.GeneralLinearGroup.map
                  ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
                    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
                      L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L)) g ∈
                AutomorphicForm.localIntegralSet L w.1 * {d w} * AutomorphicForm.localIntegralSet L w.1) ∧
          (∏ w, ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ) ^ (m w)) ≤
            (AutomorphicForm.semiLocalHaar K L v
              (AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v)).toReal ∧
          AutomorphicForm.semiLocalHaar K L v
              (AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v) ≠ ⊤ := by sorry
