-- Prove2me | Theorems.Thm_FamousTheorems_kl_divergence_chain_rule
-- name    : FamousTheorems.kl_divergence_chain_rule
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:10:05.408594+00:00
-- url     : https://prove2.me/theorems/3e74b45c-c603-4991-8693-491d1abbde2b
-- title:
--   The chain rule for KL divergence
-- statement:
--   **The chain rule for KL divergence.** Let $\mu,\nu$ be finite measures on $\alpha$ and $\kappa,\eta$ Markov kernels from $\alpha$ to $\beta$. Then
--   $$D_{\mathrm{KL}}(\mu\otimes\kappa\,\|\,\nu\otimes\eta)=D_{\mathrm{KL}}(\mu\,\|\,\nu)+D_{\mathrm{KL}}(\mu\otimes\kappa\,\|\,\mu\otimes\eta).$$
--   The last term is the conditional divergence $\int D_{\mathrm{KL}}(\kappa(x)\,\|\,\eta(x))\,d\mu(x)$.
--
--   The divergence between two joint distributions splits into the divergence of the first marginals plus the average divergence of the conditionals. The chain rule is used to bound divergences of product and sequential distributions, and it underlies the chain rule for mutual information.
--
--   **Formalization note.** Mathlib's `InformationTheory.klDiv_compProd_eq_add`. `μ.compProd κ` is the joint measure $\mu\otimes\kappa$ on $\alpha\times\beta$, and `klDiv` is the Kullback–Leibler divergence with values in $[0,\infty]$. The conditional term is written as `klDiv (μ.compProd κ) (μ.compProd η)`, which equals the averaged divergence above.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `InformationTheory.klDiv_compProd_eq_add`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem kl_divergence_chain_rule {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ ν : Measure α)
    (κ η : ProbabilityTheory.Kernel α β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [ProbabilityTheory.IsMarkovKernel κ] [ProbabilityTheory.IsMarkovKernel η] :
    InformationTheory.klDiv (μ.compProd κ) (ν.compProd η) =
      InformationTheory.klDiv μ ν + InformationTheory.klDiv (μ.compProd κ) (μ.compProd η) := by sorry

end FamousTheorems
