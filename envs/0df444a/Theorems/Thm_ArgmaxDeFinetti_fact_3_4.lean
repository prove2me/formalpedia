-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_fact_3_4
-- name    : ArgmaxDeFinetti.fact_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:15.801458+00:00
-- url     : https://prove2.me/theorems/05e6fca5-732c-426a-80e8-d36da73944ef
-- title:
--   Fact 3.4 — Takagi decomposition and symmetric tensor norms
-- statement:
--   Let $\mathcal H=\mathbb C^d$. For every $\zeta\in\mathrm{Sym}^2(\mathcal H)$,
--   $$
--   \|\zeta\|_\varepsilon=\sup_{\|v\|=1}\big|\langle v^{\otimes2},\zeta\rangle\big|=\|\mathrm{Mat}(\zeta)\|_\infty,
--   $$
--   $$
--   \|\zeta\|_\pi=\inf\Big\{\sum_k|a_k|:\ \zeta=\sum_k a_kv_k^{\otimes2},\ \|v_k\|=1\Big\}=\|\mathrm{Mat}(\zeta)\|_1 .
--   $$
--   Here $\|\cdot\|_\varepsilon$, $\|\cdot\|_\pi$ are the injective and projective norms of $\mathcal H\otimes\mathcal H$, and $\mathrm{Mat}(\zeta)$ is the complex symmetric coefficient matrix of $\zeta$. So both tensor norms of a symmetric two-tensor can be computed using symmetric rank-one tensors only.
--
--   Differences from the source:
--   - encoding: H with an orthonormal basis (e_i), Mat(ζ) in that basis → ℂ^d with its standard basis (matSym); reason: Schatten norms of Mat(ζ) are basis independent (p.25)
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Fact 3.4, p.25, eqs. (3.14)–(3.15)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_ArgmaxDeFinetti_IsSym
import Definitions.Def_ArgmaxDeFinetti_opNormS
import Definitions.Def_ArgmaxDeFinetti_injNorm
import Definitions.Def_ArgmaxDeFinetti_projNorm
import Definitions.Def_ArgmaxDeFinetti_matSym

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

/-- **Fact 3.4 (Takagi decomposition and symmetric tensor norms)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.25, eqs. (3.14)–(3.15). For every
`ζ ∈ Sym²(H)`,
`∥ζ∥_ε = sup_{∥v∥=1} |⟨v^{⊗2}, ζ⟩| = ∥Mat(ζ)∥_∞` (3.14) and
`∥ζ∥_π = inf {Σ_k |a_k| : ζ = Σ_k a_k v_k^{⊗2}, ∥v_k∥ = 1} = ∥Mat(ζ)∥₁` (3.15).

**Formalization Note** `H = ℂ^d`; `∥·∥_ε`, `∥·∥_π` are (2.13)–(2.14) on `H ⊗ H` (`pairOf ζ`); `Mat(ζ)` is (3.12) in
the standard basis (`matSym`); `∥·∥₁` is `WildeQIT.traceNorm`, `∥·∥_∞` is `opNormS`. The infimum runs over square
decompositions of every finite length. -/
theorem fact_3_4 {d : ℕ} (ζ : Vec 2 d) (hζ : IsSym ζ) :
    injNorm (pairOf ζ) = sSup {r | ∃ v : Fin d → ℂ, vnorm v = 1 ∧ r = ‖vinner (tensorPow v 2) ζ‖} ∧
    sSup {r | ∃ v : Fin d → ℂ, vnorm v = 1 ∧ r = ‖vinner (tensorPow v 2) ζ‖} = opNormS (matSym ζ) ∧
    projNorm (pairOf ζ) = sInf {r | ∃ (k : ℕ) (a : Fin k → ℂ) (v : Fin k → Fin d → ℂ),
      (∀ j, vnorm (v j) = 1) ∧ ζ = ∑ j, a j • tensorPow (v j) 2 ∧ r = ∑ j, ‖a j‖} ∧
    sInf {r | ∃ (k : ℕ) (a : Fin k → ℂ) (v : Fin k → Fin d → ℂ),
      (∀ j, vnorm (v j) = 1) ∧ ζ = ∑ j, a j • tensorPow (v j) 2 ∧ r = ∑ j, ‖a j‖} =
      WildeQIT.traceNorm (matSym ζ) := by sorry

end ArgmaxDeFinetti
