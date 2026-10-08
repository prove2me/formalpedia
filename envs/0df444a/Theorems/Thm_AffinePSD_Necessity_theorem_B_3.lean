-- Prove2me | Theorems.Thm_AffinePSD_Necessity_theorem_B_3
-- name    : AffinePSD.Necessity.theorem_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:31.998613+00:00
-- url     : https://prove2.me/theorems/762fab1f-14a2-4d09-9cc7-00cdebf01eb8
-- title:
--   Theorem B.3 — the linear hull of $\{e^{-\langle u,\cdot\rangle}: u\in S_d^{++}\}$ is dense in $\mathcal S_+$
-- statement:
--   Let $\mathcal M$ be the real linear hull of $\{f_u = \exp(-\langle u,\cdot\rangle)|_{S_d^+} : u \in S_d^{++}\}$ in $\mathcal S_+$, the space of restrictions to $S_d^+$ of rapidly decreasing smooth functions on $S_d$, topologized by the seminorms
--   $$p_{k,+}(f) = \sup_{x \in S_d^+,\ |\alpha+\beta| \le k} \big|x^\alpha\partial^\beta f(x)\big|. \qquad (B.2)$$
--   Then
--   $$\mathcal M \text{ is dense in } \mathcal S_+.$$
--
--   Combined with the closedness of the generator, this density extends the generator formula from exponentials to all of $\mathcal S_+$ in Proposition 4.12.
--
--   **Formalization Note.** Density is stated for the equivalent seminorm family $\sup_{x\in S_d^+,\, j \le k} (1+\|x\|)^k |D^j g(x)(e_1,\dots,e_j)|$ with symmetric unit directions $e_m = \tfrac12(E^{ab}+E^{ba})$: for every Schwartz $F$ on $M_d$, every $k$ and every $\varepsilon > 0$ there are finitely many $u_i \in S_d^{++}$ and reals $c_i$ with $F - \sum_i c_i e^{-\langle u_i,\cdot\rangle}$ within $\varepsilon$. Only symmetric directions enter, because derivatives of a function on $S_d^+$ in antisymmetric directions are not determined by its values on $S_d$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Theorem B.3 and the definition of M before it, p. 67; (B.2), p. 65

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Cone

open scoped SchwartzMap

namespace AffinePSD.Necessity

/-- Theorem B.3 (arXiv:0910.0137v3, App. B, p. 67): the `ℝ`-linear hull `M` of
`{f_u = exp(−⟨u, ·⟩)|_{S_d^+} : u ∈ S_d^{++}}` is dense in `S_+` (for the seminorms `p_{k,+}` of (B.2)).

**Formalization Note.** `f ∈ S_+` is `F|_{S_d^+}` for a Schwartz function `F` on `M_d`. Density is stated
for the equivalent seminorm family `sup_{x ∈ S_d^+, j ≤ k} (1 + ‖x‖)^k |D^j g(x)(e_1, …, e_j)|`, with
symmetric unit directions `e_m = (E^{ab} + E^{ba})/2`: for every `F`, `k` and `ε > 0` there is
`g = ∑ c_i e^{−⟨u_i, ·⟩}` with `u_i ∈ S_d^{++}` within `ε`. Only symmetric directions enter: derivatives
of a function on `S_d^+` in antisymmetric directions are not defined by its values on `S_d`. -/
theorem theorem_B_3 {d : ℕ} (F : 𝓢(Mat d, ℝ)) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (u : Fin n → Mat d), (∀ i, PD (u i)) ∧
      ∀ x : Mat d, PSD x → ∀ j : ℕ, j ≤ k → ∀ v : Fin j → Fin d × Fin d,
        (1 + fnorm x) ^ k *
          |iteratedFDeriv ℝ j (fun z : Mat d => F z - ∑ i, c i * Real.exp (- tr (u i) z)) x
            (fun m => symE (v m).1 (v m).2)| ≤ ε := by sorry

end AffinePSD.Necessity
