-- Prove2me | Theorems.Thm_AC02Frege_lemma_4_3_majority_ideal
-- name    : AC02Frege.lemma_4_3_majority_ideal
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:47.94755+00:00
-- url     : https://prove2.me/theorems/467456c9-4afd-4fba-90bb-76da62dde06e
-- title:
--   Lemma 4.3 — the ideal of the majority
-- statement:
--   Fix one block of $\ell=2m+1$ variables $x_1,\dots,x_\ell$, let $h=\mathrm{Maj}_\ell(x)$, and work in the Boolean ring of multilinear polynomials in these variables, where $\langle h\rangle=\{hq\}$ (products multilinearized). A monomial $x_\sigma$ is light if $|\sigma|\le m$ and heavy if $|\sigma|\ge m+1$, and $V_{\le m}$ is the span of the light monomials. Let $H_0$, $H_1$ be the inputs with at most $m$, at least $m+1$ ones.
--
--   1. The multilinear polynomial $h$ is a sum of heavy monomials, and $x_\sigma h=x_\sigma$ for every heavy monomial $x_\sigma$. The ideal $\langle h\rangle$ is exactly the span of the heavy monomials, which is also the space of functions vanishing on $H_0$; and the light monomials form a basis of the quotient by $\langle h\rangle$.
--   2. Every nonzero polynomial vanishing on $H_1$ has degree at least $m+1$. Consequently $v\mapsto hv$ is injective on $V_{\le m}$, and $\{hx_\sigma:|\sigma|\le m\}$ is a basis of $\langle h\rangle$.
--   3. Every polynomial $p$ has a unique expansion $p=u+hv$ with $\deg u,\deg v\le m$.
--
--   This one-block lemma is what makes the majority basis of the lifted variables a basis.
--
--   Differences from the source:
--   - encoding: ℓ odd, m = (ℓ − 1)/2 (standing assumption of §4) → hypothesis Odd ℓ, m = ℓ / 2; reason: same instances
--   - encoding: the Boolean ring of one block, its ideal ⟨h⟩ and the quotient by ⟨h⟩ → multilinear MvPolynomial (Fin ℓ) (ZMod 2); ⟨h⟩ = range of q ↦ ML(h q); "light monomials form a basis of the quotient" as: light monomials linearly independent, light span + ⟨h⟩ contains every multilinear p, light span ∩ ⟨h⟩ = 0; reason: these three conditions say exactly that the images of the light monomials form a basis of the quotient
--   - encoding: {h x_σ : |σ| ≤ m} is a basis of ⟨h⟩ → the family ML(h x_σ), |σ| ≤ m, is linearly independent and its span equals ⟨h⟩; reason: definition of a basis
--   - encoding: "every polynomial p", "sum of heavy monomials" → every multilinear p; every monomial s in the support of h has exponent sum > m; reason: functions are identified with their multilinear polynomials
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Lemma 4.3, p.20

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift

namespace AC02Frege

open MvPolynomial

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Lemma 4.3, p.20 (the ideal of the majority). In the Boolean ring of one block
(multilinear polynomials in the `ℓ = 2m + 1` variables `x_a`, `a : Fin ℓ`), with
`h = Maj_ℓ`, `⟨h⟩ = {ML(h q)}`, `H₀` / `H₁` the inputs with at most `m` / at least `m + 1`
ones, and `V_{≤m}` the polynomials of degree at most `m`:

(i) `h` is a sum of heavy monomials, `x_σ h = x_σ` for every heavy `x_σ`; `⟨h⟩` is the span of
the heavy monomials and also the space of functions vanishing on `H₀`; the light monomials form a
basis of the quotient by `⟨h⟩` (they are linearly independent, span everything together with
`⟨h⟩`, and their span meets `⟨h⟩` only in `0`).
(ii) Every nonzero polynomial vanishing on `H₁` has degree at least `m + 1`; `v ↦ hv` is
injective on `V_{≤m}`; `{h x_σ : |σ| ≤ m}` is a basis of `⟨h⟩`.
(iii) Every `p` has a unique expansion `p = u + hv` with `deg u, deg v ≤ m`.

**Formalization Note** `m = ℓ / 2`; `|σ|` is `σ.card`; a monomial's degree is the sum of its
exponents; products are multilinearized. Points of the cube are `x : Fin ℓ → ZMod 2`. -/
theorem lemma_4_3_majority_ideal {ℓ : ℕ} (hℓ : Odd ℓ) :
    let m := ℓ / 2
    let h := majOne ℓ
    let ideal : Set (MvPolynomial (Fin ℓ) (ZMod 2)) := Set.range (fun q => ML (h * q))
    let heavy : Submodule (ZMod 2) (MvPolynomial (Fin ℓ) (ZMod 2)) :=
      Submodule.span (ZMod 2) {p | ∃ σ : Finset (Fin ℓ), m < σ.card ∧ p = xMon σ}
    let light : Submodule (ZMod 2) (MvPolynomial (Fin ℓ) (ZMod 2)) :=
      Submodule.span (ZMod 2) {p | ∃ σ : Finset (Fin ℓ), σ.card ≤ m ∧ p = xMon σ}
    let H0 : Set (Fin ℓ → ZMod 2) := {x | (Finset.univ.filter (fun a => x a = 1)).card ≤ m}
    let H1 : Set (Fin ℓ → ZMod 2) := {x | m < (Finset.univ.filter (fun a => x a = 1)).card}
    -- (i)
    (IsMultilinear h ∧
      (∀ s ∈ h.support, m < s.sum (fun _ e => e)) ∧
      (∀ σ : Finset (Fin ℓ), m < σ.card → ML (xMon σ * h) = xMon σ) ∧
      ideal = (heavy : Set (MvPolynomial (Fin ℓ) (ZMod 2))) ∧
      ideal = {p | IsMultilinear p ∧ ∀ x ∈ H0, eval x p = 0} ∧
      LinearIndependent (ZMod 2) (fun σ : {σ : Finset (Fin ℓ) // σ.card ≤ m} => xMon σ.1) ∧
      (∀ p, IsMultilinear p → ∃ u ∈ light, ∃ w ∈ ideal, p = u + w) ∧
      (∀ u ∈ light, u ∈ ideal → u = 0)) ∧
    -- (ii)
    ((∀ p : MvPolynomial (Fin ℓ) (ZMod 2), IsMultilinear p → p ≠ 0 →
        (∀ x ∈ H1, eval x p = 0) → m + 1 ≤ p.totalDegree) ∧
      (∀ v w : MvPolynomial (Fin ℓ) (ZMod 2), IsMultilinear v → v.totalDegree ≤ m →
        IsMultilinear w → w.totalDegree ≤ m → ML (h * v) = ML (h * w) → v = w) ∧
      LinearIndependent (ZMod 2)
        (fun σ : {σ : Finset (Fin ℓ) // σ.card ≤ m} => ML (h * xMon σ.1)) ∧
      ideal = (Submodule.span (ZMod 2)
        (Set.range (fun σ : {σ : Finset (Fin ℓ) // σ.card ≤ m} => ML (h * xMon σ.1))) :
          Set (MvPolynomial (Fin ℓ) (ZMod 2)))) ∧
    -- (iii)
    (∀ p : MvPolynomial (Fin ℓ) (ZMod 2), IsMultilinear p →
      ∃! uv : MvPolynomial (Fin ℓ) (ZMod 2) × MvPolynomial (Fin ℓ) (ZMod 2),
        IsMultilinear uv.1 ∧ IsMultilinear uv.2 ∧ uv.1.totalDegree ≤ m ∧ uv.2.totalDegree ≤ m ∧
        p = uv.1 + ML (h * uv.2)) := by sorry

end AC02Frege
