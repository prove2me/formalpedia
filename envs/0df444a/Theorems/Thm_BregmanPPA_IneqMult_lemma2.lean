-- Prove2me | Theorems.Thm_BregmanPPA_IneqMult_lemma2
-- name    : BregmanPPA.IneqMult.lemma2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:06.952983+00:00
-- url     : https://prove2.me/theorems/e67c33da-3ab6-4501-857a-0128df5b84ce
-- title:
--   Lemma 2 — representations and monotonicity of the monotone conjugate
-- statement:
--   Let $h$ be a Bregman function whose zone $S$ contains the strictly positive orthant $\Omega^+$, with $\operatorname{im}(\nabla h)\supseteq\Omega^+$ (the two standing assumptions of §4.2, p. 215). Extend $h$ by $+\infty$ outside the closure of its zone. If $\delta^+$ and $\delta^-$ are the indicator functions of the nonnegative and nonpositive orthants, respectively, then for every $z$,
--
--   $$h^{*+}(z)=(h+\delta^+)^*(z)=(h^*\mathbin{\square}\delta^-)(z)=\inf_{w\ge z}h^*(w).$$
--
--   Moreover, $z\le z'$ componentwise implies $h^{*+}(z)\le h^{*+}(z')$. These identities make the orthant restriction compatible with ordinary convex conjugacy and are used throughout the analysis of recursion (11).
--
--   **Formalization Note** All conjugates and infima take values in extended reals; the source's $h$ in these identities denotes its extension outside $\overline S$. The assumption $\operatorname{im}(\nabla h)\supseteq\Omega^+$ is carried because the section states it before the lemma; the paper's proof uses only $S\supseteq\Omega^+$.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 215, Lemma 2, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_IneqMult_Program

open Filter Topology

namespace BregmanPPA.IneqMult

/-- Lemma 2, p. 215: four representations of the monotone conjugate and its monotonicity. -/
theorem lemma2 {m : ℕ} (S : Set (E m)) (h : E m → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h) (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S) :
    (∀ z : E m,
      monoConj h z = conjE (fun p => extendedH S h p + indicatorPos m p) z ∧
      monoConj h z = infConv (conjE (extendedH S h)) (indicatorNeg m) z ∧
      monoConj h z = ⨅ w ∈ {w : E m | ∀ i, z i ≤ w i}, conjE (extendedH S h) w) ∧
    (∀ z z' : E m, (∀ i, z i ≤ z' i) → monoConj h z ≤ monoConj h z') := by sorry

end BregmanPPA.IneqMult
