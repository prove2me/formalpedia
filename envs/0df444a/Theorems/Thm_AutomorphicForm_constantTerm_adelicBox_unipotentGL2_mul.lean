-- Prove2me | Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
-- name    : AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/f0625f38-edf6-53e2-a95e-44c6b8472f6c
-- title:
--   Unipotent invariance of the box constant term on GL₂(A_K)
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A}_K$, equipped with the Borel $\sigma$-algebra [`NumberField.AdelicHaar.adeleBorel`](def/NumberField_AdelicHaar.html#L132) and the additive Haar measure $\mu=$ [`NumberField.AdelicHaar.adelicAddHaar`](def/NumberField_AdelicHaar.html#L146). Let $B_K=$ [`NumberField.AdelicBox.adelicBox K`](def/NumberField_AdelicBox.html#L295) be the set of adeles whose infinite component lies in the preimage, under the identification of $\mathbb{A}_{K,\infty}$ with the mixed space, of the `ZSpan` fundamental domain of the lattice basis of $\mathcal{O}_K$, and whose finite component is integral at every height-one prime; let $\nu =$ `ProbabilityTheory.cond` $\mu\,B_K$ be the conditional measure, i.e. $\mu$ restricted to $B_K$ and normalised by $\mu(B_K)^{-1}$. For $x$ in a commutative ring write $n(x) =$ [`AutomorphicForm.unipotentGL2`](def/AutomorphicForm_ConstantTerm.html#L17) $x$, the element $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ of $\mathrm{GL}_2$ with its explicit inverse, and recall that [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47) $\nu\,n\,\varphi\,g = \int_{\mathbb{A}_K} \varphi(n(x)g)\,d\nu(x)$ (a Bochner integral, so no integrability hypothesis is imposed). Let $\varphi : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfy $\varphi(n(k)\,h)=\varphi(h)$ for every $k\in K$, where $n(k)$ is pushed into $\mathrm{GL}_2(\mathbb{A}_K)$ by [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) (entrywise $\mathrm{algebraMap}$), and every $h\in\mathrm{GL}_2(\mathbb{A}_K)$. Then for all $x_0\in\mathbb{A}_K$ and all $g\in\mathrm{GL}_2(\mathbb{A}_K)$ the two constant terms at $n(x_0)g$ and at $g$ coincide.
--
--   This is the invariance of the constant term along the unipotent radical of the standard Borel: for a function on $\mathrm{GL}_2(\mathbb{A}_K)$ invariant under the rational unipotent subgroup, the average over the box $B_K$ of the unipotent translates is a function on $N(\mathbb{A}_K)\backslash\mathrm{GL}_2(\mathbb{A}_K)$. It is used in the treatment of constant terms and pseudo-Eisenstein series, for instance in the criteria relating vanishing of the constant term almost everywhere to the vanishing of inner products against pseudo-Eisenstein series, and in the approximation results on Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul (K : Type) [Field K] [NumberField K]
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K → ℂ}
    (hφ : ∀ (k : K) (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K),
      φ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers K) K
        (AutomorphicForm.unipotentGL2 k) * h) = φ h)
    (x₀ : NumberField.AdeleRing (NumberField.RingOfIntegers K) K)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K) :
    @AutomorphicForm.constantTerm _
        (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K) _ _
        (@ProbabilityTheory.cond _
          (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K)
          (NumberField.AdelicHaar.adelicAddHaar (NumberField.RingOfIntegers K) K)
          (NumberField.AdelicBox.adelicBox K))
        (fun x => AutomorphicForm.unipotentGL2 x) φ (AutomorphicForm.unipotentGL2 x₀ * g)
      = @AutomorphicForm.constantTerm _
          (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K) _ _
          (@ProbabilityTheory.cond _
            (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K)
            (NumberField.AdelicHaar.adelicAddHaar (NumberField.RingOfIntegers K) K)
            (NumberField.AdelicBox.adelicBox K))
          (fun x => AutomorphicForm.unipotentGL2 x) φ g := by sorry
