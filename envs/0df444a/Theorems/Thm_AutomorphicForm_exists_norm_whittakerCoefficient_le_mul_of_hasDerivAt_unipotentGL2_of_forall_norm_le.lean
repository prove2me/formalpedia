-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le
-- name    : AutomorphicForm.exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/0794e7f5-6369-5f63-9b13-573d9f582a10
-- title:
--   Integration by parts bound for a Whittaker coefficient
-- statement:
--   Let $K$ be a number field, let $D \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be a set, $U$ an assignment of a subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ to each ideal of $\mathcal{O}_K$, and $\mathrm{gen}$ an assignment of an element of $\mathrm{GL}_2(\mathbb{A}_K)$ to each finite place; let $M \in \mathbb{N}$ and let $v$ lie in the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ of $K$, and assume that for some $t \in \mathbb{R}$ the standard additive character $\psi_K$ of $\mathbb{A}_K$ does not take the value $1$ at the adele whose archimedean component corresponds to $t \cdot v$ under the canonical isomorphism $\mathbb{A}_{K,\infty} \cong \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ and whose finite component is $0$. Then there is a real $c > 0$ such that for every family $xs : \mathbb{N} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, every $g \in \mathrm{GL}_2(\mathbb{A}_K)$ and every $A \in \mathbb{R}$ the following holds: if each $xs_j$ is continuous; if each $xs_j$ is invariant under left multiplication by the unipotent matrix $\begin{pmatrix}1 & \beta\\ 0 & 1\end{pmatrix}$ for every $\beta \in K$ (embedded in $\mathbb{A}_K$); if for every $j$ and every $u \in \mathbb{A}_K$ the function $t \mapsto xs_j\bigl(n(\iota(t\cdot v))\, n(u)\, g\bigr)$, where $n(\cdot)$ denotes the upper unipotent matrix and $\iota(t\cdot v)$ the adele with archimedean part $t\cdot v$ and zero finite part, has derivative $xs_{j+1}(n(u)g)$ at $t = 0$; and if $\|xs_M(n(u)g)\| \le A$ for all $u \in \mathbb{A}_K$; then the first Whittaker coefficient of $xs_0$ at $g$, namely $\int xs_0(n(u)g)\,\psi_K(-u)\,d\nu(u)$ taken with respect to the adelic additive Haar measure conditioned on the adelic box $B_\infty \times \prod_v \mathcal{O}_v$ (this being the only part of the data $D, U, \mathrm{gen}$ entering the Whittaker coefficient), satisfies $\|W(xs_0)(g)\| \le c\,A$.
--
--   This is the archimedean integration-by-parts estimate for the Fourier (Whittaker) coefficient of a function on $\mathrm{GL}_2(\mathbb{A}_K)$ along the unipotent direction $v$, stated with hypotheses matching what a smooth vector supplies along the unipotent orbit of a point, and with a constant uniform in the family, in $g$ and in $A$. It feeds the bounds on Whittaker coefficients of right convolutions in terms of idele norms and of archimedean absolute values, and thereby the decay statements used for cusp forms whose constant term vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem AutomorphicForm.exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (M : ℕ) (v : mixedEmbedding.mixedSpace K)
    (hv : ∃ t : ℝ, NumberField.StandardAddChar.stdAddChar K
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) ≠ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (xs : ℕ → AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) (A : ℝ),
        (∀ j : ℕ, Continuous (xs j)) →
        (∀ (j : ℕ) (β : K) (h : AdelicGL2 (𝓞 K) K),
          xs j (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = xs j h) →
        (∀ (j : ℕ) (u : AdeleRing (𝓞 K) K),
          HasDerivAt (fun t : ℝ => xs j (unipotentGL2 (R := AdeleRing (𝓞 K) K)
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) * (unipotentGL2 u * g)))
            (xs (j + 1) (unipotentGL2 u * g)) 0) →
        (∀ u : AdeleRing (𝓞 K) K, ‖xs M (unipotentGL2 u * g)‖ ≤ A) →
        ‖whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) (xs 0) 1 g‖ ≤ c * A := by sorry
