-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact
-- name    : AutomorphicForm.exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/c64f16a2-7f91-5fc3-8959-1ae7a8448c59
-- title:
--   Bi-finitisation of the archimedean factor of a test function
-- statement:
--   Let $F$ be a number field, let $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous, and let $f_{a,0}$ be an archimedean test factor on $\mathrm{GL}_2(\mathbb{A}_{F,\infty})$, meaning that $f_{a,0}$ has compact support and is of the form $g \mapsto \Phi(\mathrm{archEntries}\,g)$ for some $\Phi$ on $2\times 2$ matrices over the mixed space of $F$ that is $C^\infty$ over $\mathbb{R}$, where $\mathrm{archEntries}$ transports the matrix entries of $g$ through the identification of the infinite adele ring with the mixed space. Let $f_f$ be a finite test factor, i.e. a locally constant, compactly supported function on $\mathrm{GL}_2$ of the finite adeles. Write $\varphi * (f_a \otimes f_f)$ for the right convolution $g \mapsto \int \varphi(gx)\, f_a(g_\infty(x))\, f_f(g_{\mathrm{fin}}(x))\,dx$ against the Haar measure on the adelic $\mathrm{GL}_2$ (Borel $\sigma$-algebra), $g_\infty$ and $g_{\mathrm{fin}}$ being the archimedean and finite projections. Assume $\varphi * (f_{a,0} \otimes f_f)$ is non-zero at some point $g_0$; let $C$ be a compact subset of $\mathrm{GL}_2(\mathbb{A}_F)$ and $\eta > 0$. Then there exist an archimedean type family $\mathrm{tys}$ — a number $\mathrm{card}(w)$ for each infinite place $w$ of $F$ together with, for each $w$, that many representations of the determinant-one row-isometry subgroup of $\mathrm{GL}_2(F_w)$ on spaces $\mathbb{C}^n$ — and a further archimedean test factor $f_a$ such that: $f_a$ is bi-finite of type $\mathrm{tys}$, i.e. $x \mapsto f_a(x^{-1})$ lies in the archimedean factor cut submodule $\bigsqcap_w \sum_i \mathrm{archFactorTypeSubmoduleAt}$ and $f_a$ lies in the corresponding dual cut submodule; the convolution $\varphi * (f_a \otimes f_f)$ is not the zero function; it lies in the archimedean cut submodule $\bigsqcap_w \sum_i \mathrm{archTypeSubmoduleAt}\,(\mathrm{tys}.\mathrm{rep}\,w\,i)$ of functions on $\mathrm{GL}_2(\mathbb{A}_F)$; and $\|(\varphi * (f_a \otimes f_f))(g) - (\varphi * (f_{a,0} \otimes f_f))(g)\| \le \eta$ for all $g \in C$. Note that the conclusion asserts non-vanishing of the new convolution as a function, not at $g_0$.
--
--   This is the bi-finitisation (K-finite smoothing) step in the archimedean analysis of automorphic forms: an arbitrary factorisable test function may be replaced by one whose archimedean factor is finite, on both sides, under the maximal compact subgroups at the infinite places, at the cost of an arbitrarily small uniform error on a prescribed compact set and without losing non-vanishing of the convolution. No automorphy, growth or $K_\infty$-finiteness is assumed of $\varphi$; the result is used in the Langlands–Tunnell part of the development, in the identification of Laplace (Casimir) eigenvalues from Whittaker coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa₀ : IsArchTestFactor F fa₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ ≠ 0)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (η : ℝ) (hη : 0 < η) :
    ∃ (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∈ archCutSubmodule F tys ∧
        ∀ g ∈ C, ‖rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g -
            rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g‖ ≤ η := by sorry
