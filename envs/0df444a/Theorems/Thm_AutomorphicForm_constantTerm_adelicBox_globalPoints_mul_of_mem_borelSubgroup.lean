-- Prove2me | Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
-- name    : AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/535d7f50-d898-5736-9157-a61be9bbf9be
-- title:
--   Left B(K)-invariance of the box constant term
-- statement:
--   Let $K$ be a number field, and write $\mathbb{A}_K$ for its adele ring and $\mathrm{GL}_2(\mathbb{A}_K)$ for [`AutomorphicForm.AdelicGL2 (𝓞 K) K`](def/AutomorphicForm_AdelicLsXi.html#L12). Let $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be an arbitrary function, subject only to the hypothesis that $\varphi(\iota(\gamma') h) = \varphi(h)$ for every $\gamma'$ in [`AutomorphicForm.borelSubgroup K`](def/AutomorphicForm_BorelSubgroup.html#L12), that is every $\gamma' \in \mathrm{GL}_2(K)$ whose $(1,0)$ entry vanishes, and every $h \in \mathrm{GL}_2(\mathbb{A}_K)$, where $\iota =$ [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) is the map $\mathrm{GL}_2(K) \to \mathrm{GL}_2(\mathbb{A}_K)$ induced entrywise by $K \to \mathbb{A}_K$. Let $\gamma \in \mathrm{GL}_2(K)$ have vanishing $(1,0)$ entry, and let $g \in \mathrm{GL}_2(\mathbb{A}_K)$. Then the constant term $\varphi_N(h) = \int_{\mathbb{A}_K} \varphi(n(x) h)\, d\nu(x)$, where $n(x) = \bigl(\begin{smallmatrix} 1 & x \\ 0 & 1\end{smallmatrix}\bigr)$ and $\nu$ is the additive Haar measure of $\mathbb{A}_K$ (for the Borel $\sigma$-algebra) conditioned on the adelic box — the set of adeles whose infinite part lies in the preimage of the fundamental domain of the Minkowski lattice basis and whose finite part is integral at every height-one prime of $\mathcal{O}_K$ — satisfies $\varphi_N(\iota(\gamma) g) = \varphi_N(g)$. No measurability or integrability of $\varphi$ is assumed.
--
--   This is the standard left $B(K)$-invariance of the constant term along the unipotent radical, here in the form where the unipotent integral is taken against the normalised additive Haar measure on the adelic box rather than against $\mathbb{A}_K/K$. It is used in the study of the constant terms of automorphic forms on $\mathrm{GL}_2$, for instance in the criteria for vanishing of constant terms in terms of pairings against pseudo-Eisenstein series and in the truncation estimates on Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup.lean

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_BorelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField
attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
    (K : Type) [Field K] [NumberField K]
    {φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ h : AutomorphicForm.AdelicGL2 (𝓞 K) K,
      φ (AutomorphicForm.globalPoints (𝓞 K) K γ * h) = φ h)
    {γ : Matrix.GeneralLinearGroup (Fin 2) K} (hγ : γ ∈ AutomorphicForm.borelSubgroup K)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    AutomorphicForm.constantTerm
        (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
        (fun x => AutomorphicForm.unipotentGL2 x) φ (AutomorphicForm.globalPoints (𝓞 K) K γ * g)
      = AutomorphicForm.constantTerm
          (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
          (fun x => AutomorphicForm.unipotentGL2 x) φ g := by sorry
