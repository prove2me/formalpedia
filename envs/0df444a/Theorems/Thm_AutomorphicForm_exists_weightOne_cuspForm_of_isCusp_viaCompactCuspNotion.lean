-- Prove2me | Theorems.Thm_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion
-- name    : AutomorphicForm.exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/c1d7647f-9069-50ee-98ea-cbf28ee42e23
-- title:
--   From cuspidal adelic eigensystems to classical weight-one cusp forms
-- statement:
--   Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with coefficients in $\mathbb{Z}[\sqrt{-2}]$ (a level ideal of $\mathbb{Z}$, non-zero, together with families $a,b$ indexed by the finite places), and assume the project's cuspidality predicate `viaCompactCuspNotion.IsCusp ℚ Φ`, which unfolds to two clauses: first, the complexified, centre-normalised system $\Phi$ (transported along the ring homomorphism $\sqrt{-2}\mapsto \sqrt{2}\,i$ and with each $b_v$ divided by the absolute norm of $v$) admits a realisation `R` in the project's sense `SmoothCuspRealizationAt` at the compact production pins — adelic Haar measure on $\mathrm{GL}_2$ of the adeles, the centre-cut Siegel set, the level subgroups $K_1(N)$ intersected with the kernel of the archimedean projection, and the Hecke generators — such that at each real place $w$ the function $R.\mathrm{toFun}$ transforms under the determinant-one row-isometry subgroup at $w$ by the weight-one character `archWeightOneAt`, and such that for each adelic $g$ the function $z\mapsto (\mathrm{Im}\,z)^{-1}R.\mathrm{toFun}(g\cdot \iota_w(s_z))$ is holomorphic in $z$ on the upper half-plane, $s_z$ the Iwasawa section; second, $\Phi.b_v=\chi_{-3}(\mathrm{N}v)$ for all $v$ outside some finite set. Then for every finite set $T$ of naturals there are $M\neq 0$ with $3\mid M$ and $\ell\mid M$ for every non-zero $\ell\in T$, a cusp form $g$ of weight $1$ on $\Gamma_1(M)$, and $b:\mathbb{N}\to\mathbb{Z}[\sqrt{-2}]$ with: $g\mid_1\gamma=\chi_{-3}(\gamma_{11}\bmod 3)\,g$ for all $\gamma\in\Gamma_0(M)$; the $n$-th $q$-expansion coefficient of $g$ equals $\mathrm{re}(b_n)+\mathrm{im}(b_n)\sqrt{2}\,i$; $b_0=0$; $b$ is a formal Hecke eigensystem ($b_1=1$ and $b_{\ell n}+e_\ell[\ell\mid n]b_{n/\ell}=b_\ell b_n$ for primes $\ell$) for the weights $e_\ell=0$ if $\ell\mid M$ and $e_\ell=\chi_{-3}(\ell)$ otherwise; and $b_p=\Phi.a_{(p)}$ for every prime $p\nmid 3M$.
--
--   This is the adelic–classical dictionary for $\mathrm{GL}_2/\mathbb{Q}$ at weight one, in the direction that converts a cuspidal adelic eigensystem with weight-one archimedean type into a holomorphic cusp form of weight one with nebentypus $\chi_{-3}$. Compared with the textbook statement it is purely existential — no newform or multiplicity-one assertion is made — the level is allowed to grow so as to absorb $3$ and the prescribed finite set $T$ of auxiliary primes, and the coefficients are tracked through the fixed embedding $\mathbb{Z}[\sqrt{-2}]\hookrightarrow\mathbb{C}$ sending $\sqrt{-2}$ to $\sqrt{2}\,i$. It is the final step of the Langlands–Tunnell branch: it supplies the classical weight-one form in [`LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift`](thm.html#LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift), whose coefficients are the Frobenius traces of an octahedral lift of a surjective $\rho:G_{\mathbb{Q}}\to\mathrm{GL}_2(\mathbb{F}_3)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.lean

import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LanglandsTunnell_RealizationDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup EisensteinWeightOne
open scoped MatrixGroups ModularForm

theorem AutomorphicForm.exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion
    (Φ : HeckeEigensystem ℚ (ℤ√(-2))) (hΦ : AutomorphicForm.viaCompactCuspNotion.IsCusp ℚ Φ)
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
