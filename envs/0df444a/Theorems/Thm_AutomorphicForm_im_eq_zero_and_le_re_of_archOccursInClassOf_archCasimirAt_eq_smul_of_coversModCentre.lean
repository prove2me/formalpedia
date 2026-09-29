-- Prove2me | Theorems.Thm_AutomorphicForm_im_eq_zero_and_le_re_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
-- name    : AutomorphicForm.im_eq_zero_and_le_re_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/c252eb57-b50f-59b2-a945-a857265890f7
-- title:
--   Bargmann's bound for Casimir eigenvalues of class witnesses
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_F)$. Put $D=\bigcup_{x\in T}\{gx : g\in \mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2` and whose archimedean component at every infinite place has local height $\ge c$, window square $\le u^2$ and $|\det|$-invariant `archDetNorm` in $[d_1,d_2]$; assume `CoversModCentre`, i.e. every $g\in\mathrm{GL}_2(\mathbb A_F)$ satisfies $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(F)$ (embedded by `globalPoints`) and some central idelic scalar $z$. Let $\Theta$ be a Hecke eigensystem over $F$ with values in $\mathbb C$ (a nonzero level ideal together with families $a,b$ indexed by the finite places) and let $w$ be a real place of $F$. Then for all $n\in\mathbb Z$ and $\lambda\in\mathbb C$: if `ArchOccursInClassOf` holds for $D$, $\Theta$ and the stated property — that is, there are a Hecke eigensystem $\Theta'$ agreeing with $\Theta$ away from finitely many places and a genuine smooth cusp realisation $R'$ at the production pins of $D$ (formed from the level-one subgroups intersected with the finite adelic subgroup, the Hecke generators and the adelic box) for $\Theta'$, whose function $\varphi=R'.\mathrm{toFun}$ satisfies: $\varphi$ has the archimedean character at $w$ given by `archWeightCharℝ n` composed with `rowIsometrySubgroup₀Map` along the identification of $w$'s completion with $\mathbb R$; $\varphi$ is archimedean-smooth at $w$ (all the maps $e\mapsto\varphi(g\cdot\mathrm{lift}_w(e))$ are $C^\infty$ on $\{\det e\ne 0\}$); for every finite list $l$ of directions in $\{H,E,F^-\}$ the iterated derivative $l.\mathrm{foldr}\,(\mathrm{archDerivAt}\ hw)\,\varphi$ is continuous and, for all $0<e_1<e_2$, bounded on the shell $\{g : \|\det g\|_{\mathbb A}\in[e_1,e_2]\}$ (idele norm via [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19)); and $\Omega_w\varphi=\lambda\varphi$ for the Casimir operator $\Omega_w=-\bigl(\tfrac14 D_H^2-\tfrac12 D_H+D_ED_{F^-}\bigr)$ at $w$ — then $\lambda$ is real, and $\mathrm{Re}\,\lambda\ge \tfrac n2\bigl(1-\tfrac n2\bigr)$ as well as $\mathrm{Re}\,\lambda\ge -\tfrac n2\bigl(1+\tfrac n2\bigr)$.
--
--   This is Bargmann's inequality for the Casimir eigenvalue of a unitary representation of $\mathrm{GL}_2(\mathbb R)$ containing the rotation type $n$, transported to the cuspidal spectrum of $\mathrm{GL}_2$ over a number field: the two displayed lower bounds together give $\mathrm{Re}\,\lambda\ge\frac{|n|}{2}(1-\frac{|n|}{2})$, and reality of $\lambda$ comes from symmetry of $\Omega_w$ against the Petersson inner product over a fundamental domain inside a determinant shell. It feeds the positivity and rigidity statements [`AutomorphicForm.im_eq_zero_and_re_pos_and_eq_of_forall_archCasimirAt_eq_of_coversModCentre`](thm.html#AutomorphicForm.im_eq_zero_and_re_pos_and_eq_of_forall_archCasimirAt_eq_of_coversModCentre) and [`AutomorphicForm.one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre`](thm.html#AutomorphicForm.one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre), and is used in the Langlands–Tunnell part of the argument through [`LanglandsTunnell.eq_of_im_sub_eq_zero_of_re_sub_ne_zero_of_isIsotypicCuspFormAt_of_mellin_eq_archFactor_principal_of_minimalWeight`](thm.html#LanglandsTunnell.eq_of_im_sub_eq_zero_of_re_sub_ne_zero_of_isIsotypicCuspFormAt_of_mellin_eq_archFactor_principal_of_minimalWeight).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_im_eq_zero_and_le_re_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm

theorem AutomorphicForm.im_eq_zero_and_le_re_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) :
    ∀ (n : ℤ) (lam : ℂ),
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
            archCasimirAt hw φ = lam • φ) →
        lam.im = 0 ∧ ((n : ℝ) / 2) * (1 - (n : ℝ) / 2) ≤ lam.re ∧ (-(n : ℝ) / 2) * (1 + (n : ℝ) / 2) ≤ lam.re := by sorry
