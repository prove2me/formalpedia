-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_lemma2
-- name    : BregmanPPA.ProxMult.lemma2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:59.002275+00:00
-- url     : https://prove2.me/theorems/562f080b-cc92-4cde-8b43-52869f32216e
-- title:
--   Lemma 2 — h*⁺ = (h + δ⁺)* = h* □ δ⁻ = inf_{w ≥ z} h*(w), and h*⁺ is nondecreasing
-- statement:
--   Let $h$ be a Bregman function on $\mathbb R^m$ with zone $S\supseteq\Omega^+$ and $\operatorname{im}(\nabla h)\supseteq\Omega^+$ (the two standing assumptions of §4.2), extended by $+\infty$ outside $\overline S$, and let $h^{*+}(z)=\sup_{p\ge0}\{\langle p,z\rangle-h(p)\}$ be its monotone conjugate. Then for all $z\in\mathbb R^m$
--
--   $$h^{*+}(z)=(h+\delta^+)^*(z)=(h^*\,\square\,\delta^-)(z)=\inf_{w\ge z}\{h^*(w)\}.$$
--
--   Furthermore, $h^{*+}$ is nondecreasing: if $z\le z'$ componentwise, then $h^{*+}(z)\le h^{*+}(z')$.
--
--   These descriptions of the monotone conjugate are used to compute $\partial[h_p^{*+}]^*=\partial[h_p+\delta^+]$ in the proof of Theorem 8, and its monotonicity is the hypothesis of the chain rule, Lemma A4.
--
--   **Formalization Note** All four quantities are `EReal`-valued; $h$ in the conjugates is the extension $\hat h$ (`extendedH S h`), which agrees with $h$ on $\overline S\supseteq\overline{\Omega^+}$. The infimum over $w\ge z$ is an `EReal` infimum over the componentwise upper set of $z$.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 215, Lemma 2

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program

open Filter Topology

namespace BregmanPPA.ProxMult

/-- Lemma 2, p. 215: `h*⁺ = (h + δ⁺)* = h* □ δ⁻ = inf_{w ≥ z} h*(w)`, and `h*⁺` is
nondecreasing; here `h` is a Bregman function on `ℝᵐ` satisfying the two standing assumptions
of §4.2 (zone `S ⊇ Ω⁺`, `im ∇h ⊇ Ω⁺`), extended by `+∞` off `S̄`. -/
theorem lemma2 {m : ℕ} (S : Set (BregmanPPA.IneqMult.E m)) (h : BregmanPPA.IneqMult.E m → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h) (hS : BregmanPPA.IneqMult.posOrthant m ⊆ S)
    (him : BregmanPPA.IneqMult.posOrthant m ⊆ gradient h '' S) :
    (∀ z : BregmanPPA.IneqMult.E m,
      BregmanPPA.IneqMult.monoConj h z = BregmanPPA.IneqMult.conjE (fun p => BregmanPPA.IneqMult.extendedH S h p + BregmanPPA.IneqMult.indicatorPos m p) z ∧
      BregmanPPA.IneqMult.monoConj h z = BregmanPPA.IneqMult.infConv (BregmanPPA.IneqMult.conjE (BregmanPPA.IneqMult.extendedH S h)) (BregmanPPA.IneqMult.indicatorNeg m) z ∧
      BregmanPPA.IneqMult.monoConj h z = ⨅ w ∈ {w : BregmanPPA.IneqMult.E m | ∀ i, z i ≤ w i}, BregmanPPA.IneqMult.conjE (BregmanPPA.IneqMult.extendedH S h) w) ∧
    (∀ z z' : BregmanPPA.IneqMult.E m, (∀ i, z i ≤ z' i) → BregmanPPA.IneqMult.monoConj h z ≤ BregmanPPA.IneqMult.monoConj h z') := by sorry

end BregmanPPA.ProxMult
