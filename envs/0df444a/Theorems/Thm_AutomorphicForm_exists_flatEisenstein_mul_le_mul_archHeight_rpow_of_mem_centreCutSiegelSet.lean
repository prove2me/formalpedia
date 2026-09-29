-- Prove2me | Theorems.Thm_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet
-- name    : AutomorphicForm.exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/2203f83b-ebc2-5bd1-b427-f6760025f369
-- title:
--   Flat Eisenstein series bounded on centre-cut Siegel sets
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$, let $t \in GL_2(\mathbb{A}_F)$ (with the adele ring $\mathbb{A}_F$ of $F$ carrying its Borel $\sigma$-algebra), and let $\sigma$ be a real number with $\sigma > 1/2$. Write $H =$ `adelicHeight F` for the function on $GL_2(\mathbb{A}_F)$ given by $H(g) = \big(\prod_{v \mid \infty} (|\det g_v| / \mathrm{rowNormSq}\, g_v)^{m_v}\big)\cdot \prod_{v \nmid \infty} \mathrm{finLocalHeight}(g_v)$, where $m_v$ is the multiplicity of the infinite place $v$ and the finite product is a `finprod` over the height-one spectrum of $\mathcal{O}_F$; write $H_\infty$ = `archHeight F` for the archimedean factor alone, $w$ for the image in $GL_2(\mathbb{A}_F)$ of the global matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and $n(\xi)$ for $\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$ with $\xi \in F$ embedded in $\mathbb{A}_F$. Then there exists a real constant $C$ such that for every $s$ in the centre-cut Siegel set $\mathfrak{S}(c,u,d_1,d_2)$ — that is, every $s$ whose finite part lies in `finiteIntegralGL2 (𝓞 F) F`, whose component at each infinite place $v$ satisfies $|\det s_v|/\mathrm{rowNormSq}\, s_v \ge c$ and $\mathrm{topNormSq}\, s_v/\mathrm{rowNormSq}\, s_v - (|\det s_v|/\mathrm{rowNormSq}\, s_v)^2 \le u^2$, and for which `archDetNorm` at each infinite place lies in $[d_1,d_2]$ — the family $\xi \mapsto H(w\,n(\xi)\,st)^{\sigma + 1/2}$ is summable over $\xi \in F$ and
--   $$H(st)^{\sigma+1/2} + \sum_{\xi \in F} H(w\,n(\xi)\,st)^{\sigma+1/2} \le C \cdot H_\infty(s)^{\sigma+1/2}.$$
--   The constant is uniform over the Siegel set, but may depend on $F, c, u, d_1, d_2, t$ and $\sigma$; note that the right-hand side involves the archimedean height of $s$ only, not of $st$.
--
--   This is the moderate-growth estimate for the flat spherical Eisenstein series at a real spectral parameter: on a Siegel set cut by a height floor, a window bound and a bound on the determinant norms, the Bruhat-form series is dominated by a constant multiple of the archimedean height raised to $\sigma + 1/2$. It is the growth input used for the $L^p$ bounds on pseudo-Eisenstein functions, for the finite-support statement for pseudo-Eisenstein summands, and for the construction of Rankin–Selberg test data with analytic local integrals; the proof cites the identification of $H^{s+1/2}$ as an induced section, summability of the Bruhat transversal sum for $\operatorname{Re} s > 1/2$, and continuity of the adelic height.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (t : AdelicGL2 (𝓞 F) F)
    (σ : ℝ) (hσ : 1 / 2 < σ) :
    letI := adeleBorel (𝓞 F) F
    ∃ C : ℝ, ∀ s ∈ centreCutSiegelSet F c u d₁ d₂,
      Summable (fun ξ : F => adelicHeight F (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ (σ + 1 / 2)) ∧
      adelicHeight F (s * t) ^ (σ + 1 / 2)
          + ∑' ξ : F, adelicHeight F (adelicWeyl (𝓞 F) F
              * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ (σ + 1 / 2)
        ≤ C * archHeight F (glArch (𝓞 F) F s) ^ (σ + 1 / 2) := by sorry
