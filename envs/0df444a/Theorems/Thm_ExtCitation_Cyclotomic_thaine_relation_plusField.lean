-- Prove2me | Theorems.Thm_ExtCitation_Cyclotomic_thaine_relation_plusField
-- name    : ExtCitation.Cyclotomic.thaine_relation_plusField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/0aca78fe-50e9-53b0-8459-ed64cd429378
-- title:
--   A Thaine relation for a degree-one prime of K⁺
-- statement:
--   Let $p\ge 5$ be a prime and let $K^{+}$ be a totally real number field carrying an algebra structure making $\mathbb{Q}(\zeta_p)=$ `CyclotomicField p ℚ` an extension of $K^{+}$ of degree $2$. Let $\Delta\mathrm{act}\colon(\mathbb{Z}/p)^{\times}\to\operatorname{Aut}_{\mathrm{ring}}(\mathcal{O}_{K^{+}})$ be a monoid homomorphism which is compatible, via the structure map $\mathcal{O}_{K^{+}}\to\mathcal{O}_{\mathbb{Q}(\zeta_p)}$, with the action `clRingAction` of $(\mathbb{Z}/p)^{\times}$ on $\mathcal{O}_{\mathbb{Q}(\zeta_p)}$ obtained by transporting the restriction to rings of integers of the Galois group along the inverse of the cyclotomic character isomorphism $(\mathbb{Q}(\zeta_p)\simeq_{\mathbb{Q}}\mathbb{Q}(\zeta_p))\cong(\mathbb{Z}/p)^{\times}$. Let $\ell\neq p$ be a prime and $\mathfrak{L}$ a maximal ideal of $\mathcal{O}_{K^{+}}$ with absolute norm $\ell$. Let $\delta\in\mathcal{O}_{K^{+}}^{\times}$ satisfy: for every $d\in(\mathbb{Z}/p)^{\times}$ there is a unit $v$ with $\Delta\mathrm{act}(d)(\delta)=\delta^{\,(d^{2}).\mathrm{val}}\,v^{p}$, and the image of $\delta$ in $\mathcal{O}_{K^{+}}/\mathfrak{L}$ is not a $p$-th power. Then there exist $\alpha\in K^{+}$ with $\alpha\neq 0$, $t\in\mathbb{Z}/p$ with $t\neq 0$, and an ideal $J$ of $\mathcal{O}_{K^{+}}$ such that, as fractional ideals of $\mathcal{O}_{K^{+}}$ in $K^{+}$, $$(\alpha)=\prod_{d\in(\mathbb{Z}/p)^{\times}}\bigl(\Delta\mathrm{act}(d)(\mathfrak{L})\bigr)^{(t\,(d^{2})^{-1}).\mathrm{val}}\cdot J^{p},$$ the exponents being the representatives in $\{0,\dots,p-1\}$ of the indicated residues.
--
--   This is the per-prime relation underlying Thaine's theorem: the existence of an $\omega^{2}$-eigen-unit which is not a $p$-th power modulo a degree-one prime $\mathfrak{L}$ produces a principal-ideal relation expressing that the $\omega^{2}$-component of the class of $\mathfrak{L}$ is trivial in $\mathrm{Cl}(K^{+})/p$. It is used to prove that the $\omega^{2}$-eigenspace of the $p$-torsion of the class group of the real cyclotomic field vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_Cyclotomic_thaine_relation_plusField.lean

import Definitions.Def_ClassGroup_GaloisAction
import Definitions.Def_Stickelberger_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ExtCitation.Cyclotomic
open NumberField JacobiSumStickelberger Stickelberger
variable (p : ℕ) [Fact p.Prime]

theorem thaine_relation_plusField (hp5 : 5 ≤ p)
    (Kplus : Type*) [Field Kplus] [NumberField Kplus] [IsTotallyReal Kplus]
    [Algebra Kplus (CyclotomicField p ℚ)]
    (hKplus : Module.finrank Kplus (CyclotomicField p ℚ) = 2)
    (Δact : (ZMod p)ˣ →* (𝓞 Kplus) ≃+* (𝓞 Kplus))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).comp
      (Δact d).toRingHom = (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (𝔏 : Ideal (𝓞 Kplus)) (h𝔏max : 𝔏.IsMaximal)
    (h𝔏deg : Ideal.absNorm 𝔏 = ℓ)
    (δ : (𝓞 Kplus)ˣ)
    (hδeig : ∀ d : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
      Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p)
    (hδ𝔏 : (Ideal.Quotient.mk 𝔏 (δ : 𝓞 Kplus))
      ∉ {x : 𝓞 Kplus ⧸ 𝔏 | ∃ y, y ^ p = x}) :
    ∃ (α : Kplus) (_hα : α ≠ 0) (t : ZMod p) (_ht : t ≠ 0) (J : Ideal (𝓞 Kplus)),
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 Kplus)) α =
        (∏ d : (ZMod p)ˣ, (𝔏.map (Δact d).toRingHom :
          FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^
            (t * ((d : ZMod p) ^ 2)⁻¹).val) *
        (J : FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^ p := by sorry
