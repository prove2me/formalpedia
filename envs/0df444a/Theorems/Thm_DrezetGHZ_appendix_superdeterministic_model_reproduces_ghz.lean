-- Prove2me | Theorems.Thm_DrezetGHZ_appendix_superdeterministic_model_reproduces_ghz
-- name    : DrezetGHZ.appendix_superdeterministic_model_reproduces_ghz
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T21:10:53.818496+00:00
-- url     : https://prove2.me/theorems/88c34ec6-6a31-4f12-9d84-a45832dd3e66
-- title:
--   Appendix 3, Eqs. (39)–(45): a setting-dependent beable model reproduces the GHZ predictions
-- statement:
--   Consider the model of Appendix 3. The beables are angle triples $(\theta_1,\theta_2,\theta_3)$. The local responses are
--   $$P_j(\alpha\mid\theta_j,\hat x)=\tfrac{1+\alpha\cos\theta_j}{2},\qquad P_j(\alpha\mid\theta_j,\hat y)=\tfrac{1+\alpha\sin\theta_j}{2}\qquad\text{(Eq. (43)),}$$
--   and the setting-dependent density is
--   $$\rho(\cdot\mid\hat n_1,\hat n_2,\hat n_3)=\tfrac14\sum_{v_1v_2v_3=s}\delta_{(\vartheta(\hat n_1,v_1),\vartheta(\hat n_2,v_2),\vartheta(\hat n_3,v_3))}\qquad\text{(Eqs. (44)–(45)),}$$
--   where $s=-1$ for $(\hat x,\hat x,\hat x)$, $s=+1$ for the other three GHZ settings, and $\vartheta(\pm\hat x)\in\{0,\pi\}$, $\vartheta(\pm\hat y)=\pm\pi/2$ are polar angles.
--
--   Then for each of the four GHZ settings $(\hat n_1,\hat n_2,\hat n_3)$ and all $\alpha,\beta,\gamma\in\{\pm1\}$,
--   $$\int P_1(\alpha\mid\theta_1,\hat n_1)P_2(\beta\mid\theta_2,\hat n_2)P_3(\gamma\mid\theta_3,\hat n_3)\,d\rho(\theta\mid\hat n_1,\hat n_2,\hat n_3)=P(\alpha,\beta,\gamma\mid\hat n_1,\hat n_2,\hat n_3,\psi)$$
--   (Eqs. (39)–(42)).
--
--   The model keeps the local factorization of Eq. (17) and gives up statistical independence (Eq. (18)). This is the paper's example that the GHZ correlations can be reproduced once superdeterminism is allowed.
-- source:
--   A. Drezet, "An Elementary Proof That Everett's Quantum Multiverse Is Nonlocal: Bell-Locality and Branch-Symmetry in the Many-Worlds Interpretation", arXiv:2306.07794v1 [quant-ph] (2023), https://arxiv.org/abs/2306.07794, pp. 21–22, Appendix 3, Eqs. (39)–(45); discussed on p. 13 around Eq. (33).

import Mathlib
import Definitions.Def_DrezetGHZ_Models
open MeasureTheory

namespace DrezetGHZ
theorem appendix_superdeterministic_model_reproduces_ghz (n₁ n₂ n₃ : Setting)
    (hn : (n₁, n₂, n₃) ∈ ({(.x, .x, .x), (.x, .y, .y), (.y, .x, .y), (.y, .y, .x)} :
      Finset (Setting × Setting × Setting)))
    (α β γ : ℤˣ) :
    ∫ θ, appendixResponse θ.1 n₁ α * appendixResponse θ.2.1 n₂ β *
        appendixResponse θ.2.2 n₃ γ ∂(appendixDensity n₁ n₂ n₃) =
      bornProb n₁ n₂ n₃ α β γ := by sorry
end DrezetGHZ
