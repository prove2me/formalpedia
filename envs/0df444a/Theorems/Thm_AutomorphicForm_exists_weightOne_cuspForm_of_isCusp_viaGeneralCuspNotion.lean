-- Prove2me | Theorems.Thm_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaGeneralCuspNotion
-- name    : AutomorphicForm.exists_weightOne_cuspForm_of_isCusp_viaGeneralCuspNotion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/4009ddd9-ce5e-5812-9a34-3d246f22fac6
-- title:
--   Weight-one cusp form from a cuspidal Hecke eigensystem over ℚ
-- statement:
--   Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with values in $\mathbb{Z}[\sqrt{-2}]$, that is, a nonzero ideal $\Phi.\mathrm{level}$ of $\mathcal{O}_{\mathbb{Q}}$ together with functions $a,b$ on the finite places, and assume `AutomorphicForm.viaGeneralCuspNotion.IsCusp ℚ Φ`: the complex eigensystem obtained by pushing $\Phi$ along the embedding $\sqrt{-2}\mapsto\sqrt{2}\,i$ and replacing its $b$-values by $(\mathrm{cNorm}\,v)^{-1}b_v$ admits a smooth cusp realisation $R$ on $\mathrm{GL}_2$ of the adèles of $\mathbb{Q}$ at the pins `productionPinsGeneral ℚ` (a function nonvanishing somewhere, invariant under the level subgroup, with central character, Hecke eigenvalue $a_v$ and central eigenvalue outside a finite exceptional set) such that $R$ is continuous, satisfies at each real place the weight-one character `archWeightOneAt` on `rowIsometrySubgroup₀`, and has, for each adelic $g$, the function $z\mapsto(\operatorname{Im}z)^{-1}R(g\cdot s_z)$ differentiable on the upper half-plane for the Iwasawa section $s_z$; moreover $\Phi.b_v=\chi_{-3}(\mathrm{N}v)$ for all $v$ outside a finite set. Let $T$ be a finite set of naturals. Then there is a level $M\neq 0$ with $3\mid M$ and $\ell\mid M$ for every nonzero $\ell\in T$, a cusp form $g$ of weight $1$ on $\Gamma_1(M)$ and $b:\mathbb{N}\to\mathbb{Z}[\sqrt{-2}]$ with: $g\mid[1]\gamma=\chi_{-3}(\gamma_{22}\bmod 3)\,g$ for all $\gamma\in\Gamma_0(M)$; the $n$-th coefficient of the $q$-expansion of $g$ equals the image of $b_n$ under $\sqrt{-2}\mapsto\sqrt2\,i$; $b_0=0$; $b$ is a formal Hecke eigensystem ($b_1=1$ and $b_{\ell n}+e_\ell\cdot[\ell\mid n]b_{n/\ell}=b_\ell b_n$ for all primes $\ell$) for the character $e_\ell=0$ if $\ell\mid M$ and $e_\ell=\chi_{-3}(\ell)$ otherwise; and $b_p=\Phi.a$ at the place of $\mathcal{O}_{\mathbb{Q}}$ attached to $p$ for every prime $p\nmid 3M$.
--
--   This is the adèlic-to-classical dictionary at weight one for $\mathrm{GL}_2/\mathbb{Q}$: an automorphic eigensystem with weight-one archimedean behaviour and $\chi_{-3}$-type central data is converted into a holomorphic weight-one cusp form with nebentypus $\chi_{-3}$ whose $q$-coefficients lie in $\mathbb{Z}[\sqrt{-2}]$ and match the given Hecke eigenvalues away from $3M$, with the level allowed to absorb any prescribed finite set of primes. It feeds the construction of Langlands–Tunnell lifts, being cited by [`LanglandsTunnell.exists_liftValued_of_agreesLiftTraceSeed_isCusp_pair`](thm.html#LanglandsTunnell.exists_liftValued_of_agreesLiftTraceSeed_isCusp_pair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaGeneralCuspNotion.lean

import Definitions.Def_AutomorphicForm_ViaGeneralCuspNotion
import Definitions.Def_LanglandsTunnell_RealizationDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup EisensteinWeightOne
open scoped MatrixGroups ModularForm

theorem AutomorphicForm.exists_weightOne_cuspForm_of_isCusp_viaGeneralCuspNotion
    (Φ : HeckeEigensystem ℚ (ℤ√(-2))) (hΦ : AutomorphicForm.viaGeneralCuspNotion.IsCusp ℚ Φ)
    (T : Finset ℕ) :
    ∃ (M : ℕ) (_ : NeZero M), 3 ∣ M ∧ (∀ ℓ ∈ T, ℓ ≠ 0 → ℓ ∣ M) ∧
      ∃ (g : CuspForm (Gamma1 M) 1) (b : ℕ → ℤ√(-2)),
        (∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
          (⇑g) ∣[(1 : ℤ)] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑g)) ∧
        (∀ n, ModularFormClass.qCoeff (⇑g) n =
          ((b n).re : ℂ) + ((b n).im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I)) ∧
        b 0 = 0 ∧
        FormalHecke.IsEigensystem
          (fun ℓ => if ℓ ∣ M then (0 : ℤ√(-2)) else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
        ∀ (p : ℕ) (hp : p.Prime), ¬ p ∣ 3 * M → b p = Φ.a (AutomorphicForm.ratPrime ⟨p, hp⟩) := by sorry
