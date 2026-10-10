-- Prove2me | Theorems.Thm_BypassMonster_Falcon_lemma_A_3
-- name    : BypassMonster.Falcon.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:32.635486+00:00
-- url     : https://prove2.me/theorems/f1d056dd-8f37-4ead-a8c2-e698e090fe29
-- title:
--   Lemma A.3, p. 1923 — pₘ is an action selection kernel and Qₘ = ∏ₓ pₘ(·|x) is a probability on Ψ with pₘ(a|x) = Σ_π 𝕀{π(x)=a}Qₘ(π)
-- statement:
--   Fix an epoch $m\ge1$ and an outcome of the run. The action selection scheme $p_m(\cdot\mid\cdot)$ of FALCON+ (step 6 of Algorithm 2) is a valid action selection kernel: $p_m(a\mid x)\ge0$ and $\sum_a p_m(a\mid x)=1$ for every context $x$. Moreover, the product $Q_m(\pi)=\prod_{x\in\mathcal X}p_m(\pi(x)\mid x)$ is a probability distribution on the universal policy space $\Psi=\mathcal A^{\mathcal X}$ that induces $p_m$:
--   $$\forall a\in\mathcal A,\ \forall x\in\mathcal X,\qquad p_m(a\mid x)=\sum_{\pi\in\Psi}\mathbb 1\{\pi(x)=a\}\,Q_m(\pi).$$
--
--   This translates the algorithm's per-context randomization into a single randomized policy, the "equivalent randomized policy" through which the rest of the analysis runs.
--
--   **Formalization Note** The paper asserts that some such $Q_m$ exists; the statement is made for the specific product $Q_m$ that its proof constructs and every later lemma uses, which is stronger. The only hypothesis is that the tie-breaking rule picks a maximizer of $\hat f_m(x,\cdot)$. $\mathcal X$ is finite (the paper's proof is for $|\mathcal X|<\infty$).
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), Lemma A.3 and its proof, p. 1923

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model
import Definitions.Def_BypassMonster_Falcon_Analysis

namespace BypassMonster.Falcon

/-- **Lemma A.3** (p. 1923): for every epoch `m ≥ 1` and every outcome `ω`, the action selection
scheme `p_m(· | ·)` is a valid action selection kernel, and the product `Q_m = ∏_x p_m(· | x)` is a
probability distribution on the universal policy space `Ψ = 𝒜^X` with
`p_m(a | x) = ∑_{π ∈ Ψ} 𝕀{π(x) = a} Q_m(π)` for all `a`, `x`. -/
theorem lemma_A_3
    {X : Type*} [Fintype X] [DecidableEq X]
    {K : ℕ} [NeZero K]
    (A : Params X K) (hamax : ∀ (g : Fin K → ℝ) (a : Fin K), g a ≤ g (A.amax g))
    (m : ℕ) (hm : 1 ≤ m) (ω : Params.Omega X K) :
    IsSelKernel (A.pm m ω) ∧
    ((∀ π : X → Fin K, 0 ≤ A.Qm m ω π) ∧ ∑ π : X → Fin K, A.Qm m ω π = 1) ∧
    ∀ (a : Fin K) (x : X), A.pm m ω x a = ∑ π : X → Fin K, if π x = a then A.Qm m ω π else 0 := by sorry

end BypassMonster.Falcon
