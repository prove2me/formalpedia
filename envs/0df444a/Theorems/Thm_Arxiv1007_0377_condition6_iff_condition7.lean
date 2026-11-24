-- Prove2me | Theorems.Thm_Arxiv1007_0377_condition6_iff_condition7
-- name    : Arxiv1007_0377.condition6_iff_condition7
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T00:01:58.770958+00:00
-- url     : https://prove2.me/theorems/47ce676d-f8be-4393-8032-91e92d6469f9
-- title:
--   Eq. (7): simplification of the non-analyticity condition (6) (as proved)
-- statement:
--   Let $\epsilon=\epsilon_r+i\epsilon_i$ and $\mu=\mu_r+i\mu_i$ be complex numbers with $\mu_i\neq0$. Consider condition (6),
--
--   $$\epsilon_r\mu_r-\epsilon_i\mu_i+|\epsilon||\mu|=0,$$
--
--   and condition (7),
--
--   $$\epsilon_r=-\frac{\epsilon_i\mu_r}{\mu_i}.$$
--
--   Then (6) implies (7). Moreover, (6) holds if and only if (7) holds and $\epsilon_r\mu_r-\epsilon_i\mu_i\le0$. In other words, (6) says exactly that $\epsilon\mu$ is a real number $\le0$, and (7) says exactly that $\epsilon\mu$ is real.
--
--   Condition (7) is the paper's criterion, in terms of $\epsilon$ and $\mu$, for the frequencies at which the refractive index must switch between the branches $n_+$ and $n_-$.
--
--   **Formalization Note** The paper says that (6) "simplifies to" (7) and treats them as equivalent. That is false: for $\epsilon=1-i$ and $\mu=1+i$, condition (7) holds but $\epsilon_r\mu_r-\epsilon_i\mu_i+|\epsilon||\mu|=4$. The statement keeps the implication that the paper's derivation gives, (6) $\Rightarrow$ (7), and adds the sign condition that is lost in the derivation, which gives the exact equivalence. The hypothesis $\mu_i\neq0$ is implicit in the paper's division by $\mu_i$.
-- source:
--   Hickey, Akyurtlu and Kussow, Relationship between the Kramers-Kronig relations and negative index of refraction, arXiv:1007.0377v2 (2010), claim c014; main text, eqs. (6) and (7), PDF p. 2; abstract, PDF p. 1

import Mathlib
import Definitions.Def_Arxiv1007_0377_Basic

open Complex Polynomial

namespace Arxiv1007_0377

theorem condition6_iff_condition7 (ε μ : ℂ) (hμ : μ.im ≠ 0) :
    (Condition6 ε μ → Condition7 ε μ) ∧
    (Condition6 ε μ ↔ Condition7 ε μ ∧ epsMuRe ε μ ≤ 0) := by sorry

end Arxiv1007_0377
