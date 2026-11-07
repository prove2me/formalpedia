-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_lemma_3_3
-- name    : ArgmaxDeFinetti.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:46.62627+00:00
-- url     : https://prove2.me/theorems/99d5ed61-c50c-4465-bbc9-2c06f3915be1
-- title:
--   Lemma 3.3 — complex-sphere argmax estimate
-- statement:
--   Let $N=2+m\ge2$, $\mathcal H=\mathbb C^d$, let $\psi\in\mathrm{Sym}^N(\mathcal H)$ be a unit vector, and let $u$ be a unit vector maximizing $|\langle v^{\otimes N},\psi\rangle|$ over the unit sphere, with $c=\langle u^{\otimes N},\psi\rangle>0$. Let $\eta_u=(\langle u|^{\otimes(N-2)}\otimes I_{\mathcal H^{\otimes2}})\psi$. Then
--   $$
--   \eta_u=c\,u^{\otimes2}+\zeta_u,\qquad \zeta_u\in\mathrm{Sym}^2(u^\perp),
--   $$
--   and
--   $$
--   \sup_{\substack{v\perp u\\ \|v\|=1}}\big|\langle v^{\otimes2},\zeta_u\rangle\big|\le\frac{c}{N-1}.
--   $$
--   First-order optimality of $u$ removes the mixed $u\vee u^\perp$ component of $\eta_u$, and second-order optimality bounds its $\mathrm{Sym}^2(u^\perp)$ component on every square $v^{\otimes2}$.
--
--   Differences from the source:
--   - encoding: N ≥ 2 → N = 2 + m with m : ℕ; reason: the same values of N
--   - encoding: η_u = (⟨u|^⊗(N−2) ⊗ I)ψ contracts the first N − 2 sites → etaU contracts sites 3, …, N and keeps sites 1, 2; reason: ψ is symmetric, so both give the same vector
--   - encoding: η_u = c u^⊗2 + ζ_u with ζ_u ∈ Sym²(u⊥), and sup over unit v ⊥ u ≤ c/(N − 1) → ζ_u := η_u − c u^⊗2 lies in Sym²(u⊥) (InSym2Perp), and the bound holds for every unit v with ⟨u, v⟩ = 0; reason: ζ_u is determined by (3.8); a supremum is ≤ a bound iff every element is
--   - encoding: "with the notation above" → hypotheses: ψ unit and symmetric, u a unit argmax of |⟨v^⊗N, ψ⟩|, ⟨u^⊗N, ψ⟩ = c > 0; reason: the notation fixed on pp.22–23 before the lemma
--   - encoding: H → ℂ^d; reason: a finite-dimensional complex Hilbert space in an orthonormal basis
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Lemma 3.3, p.23, eqs. (3.8)–(3.9)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_ArgmaxDeFinetti_IsSym
import Definitions.Def_ArgmaxDeFinetti_etaU
import Definitions.Def_ArgmaxDeFinetti_InSym2Perp

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

/-- **Lemma 3.3 (Complex-sphere argmax estimate)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.23, eqs. (3.8)–(3.9).

Let `ψ ∈ Sym^N(H)` be a unit vector, `u` a unit vector maximizing `|⟨v^{⊗N}, ψ⟩|` over the unit sphere, with
`c = ⟨u^{⊗N}, ψ⟩ > 0`, and `η_u` as in (3.7). Then `η_u = c u^{⊗2} + ζ_u` with `ζ_u ∈ Sym²(u⊥)` (3.8), and
`sup_{v⊥u, ∥v∥=1} |⟨v^{⊗2}, ζ_u⟩| ≤ c/(N − 1)` (3.9).

**Formalization Note** `N = 2 + m`, `H = ℂ^d`. "With the notation above" (pp.22–23) is the hypotheses `hψ`, `hψn`,
`hu`, `hmax`, `hc`, `hcpos`. `ζ_u` is `η_u − c u^{⊗2}`, so (3.8) is `InSym2Perp u (η_u − c u^{⊗2})`. The supremum
bound (3.9) is stated pointwise for every unit `v` with `⟨u, v⟩ = 0`. `η_u` keeps sites `1, 2` (see `etaU`). -/
theorem lemma_3_3 {m d : ℕ} (ψ : Vec (2 + m) d) (hψ : IsSym ψ) (hψn : vnorm ψ = 1)
    (u : Fin d → ℂ) (hu : vnorm u = 1)
    (hmax : ∀ v : Fin d → ℂ, vnorm v = 1 →
      ‖vinner (tensorPow v (2 + m)) ψ‖ ≤ ‖vinner (tensorPow u (2 + m)) ψ‖)
    (c : ℝ) (hc : vinner (tensorPow u (2 + m)) ψ = c) (hcpos : 0 < c) :
    InSym2Perp u (etaU u ψ - (c : ℂ) • tensorPow u 2) ∧
      ∀ v : Fin d → ℂ, vinner u v = 0 → vnorm v = 1 →
        ‖vinner (tensorPow v 2) (etaU u ψ - (c : ℂ) • tensorPow u 2)‖ ≤ c / (((2 + m : ℕ) : ℝ) - 1) := by sorry

end ArgmaxDeFinetti
