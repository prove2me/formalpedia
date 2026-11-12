-- Prove2me | Theorems.Thm_DIObliviousTransfer_theorem_20
-- name    : DIObliviousTransfer.theorem_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:08:22.27357+00:00
-- url     : https://prove2.me/theorems/f43e1908-4bb7-45f5-b0be-f77f6900833e
-- title:
--   Theorem 20 — efficient sequential composition
-- statement:
--   Let QPT protocols $P_f$ and $P^f_g$ realize $f$ and $g$ (Definition 5), with simulator maps $\mathrm{sim}_f,\mathrm{sim}_g$, and suppose $P^f_g$ makes at most $q(\lambda)\le\mathrm{poly}(\lambda)$ ideal-$f$ calls, all with valid inputs. Replacing the calls by $P_f$ on fresh batches and budget groups gives a protocol $P^{P_f}_g$ with the following properties.
--   1. It realizes $g$.
--   2. For every QPT adversary and test there are induced QPT outer and call adversaries and tests with
--   $$\mathrm{Adv}\le\nu_g+q\,\nu_f,$$
--   where $\nu_g,\nu_f$ are their advantages against $\mathrm{sim}_g,\mathrm{sim}_f$, uniform over admissible extensions and inputs.
--   3. $\varepsilon^{\mathrm{cor}}\le\varepsilon^{\mathrm{cor}}_g+q\,\varepsilon^{\mathrm{cor}}_f$.
--
--   Differences from the source:
--
--   - encoding: composition at invocation boundaries satisfying Definition 6 in every replacement hybrid → ideal calls replaced by fresh copies of the subprotocol on fresh batches with fresh budget groups; Definition 6 holds by construction of the execution semantics; reason: Decision D11 (Definition 6, Theorem 20)
--   - reading: nonuniform QPT adversaries, devices and simulators with polynomial-size quantum advice → families of machines whose activations are circuits of at most two-qubit unitaries and single-wire resets with classical input loaded and output measured, all sizes bounded by one polynomial in λ; advice is part of the arbitrary initial state; reason: Decision D3 (pp.2, 17): one standard reading of nonuniform QPT
--   - reading: Real ≈c Ideal, the negligible advantage bound uniform over admissible η and fixed honest inputs → for every polynomially bounded reference size and every QPT test there is one negligible ε with advantage at most ε(λ) for every λ, every admissible η and every valid honest input; reason: Decision D4 (Definition 5 (ii)); the stronger, uniform reading
--   - generalization: independent honest quantum coordinate implementations with loss at most q_dev for every question pair (3) → honest devices given by independent per-coordinate conditional answer distributions with loss at most q_dev, not required to be quantum or no-signalling; reason: Decision D12: correctness uses only (3) and independence (Claim 3); quantum devices are a special case
--   - encoding: joint output–reference trace-distance correctness errors → total variation distance between the honest output distributions of the real and ideal honest executions; reason: honest executions of these protocols have no reference; the paper notes the two coincide for the OT instantiations (p.59)
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Theorem 20, p.58 (PDF p.60)

import Mathlib
import Definitions.Def_DIObliviousTransfer_Realizes

namespace DIObliviousTransfer

/-- **Theorem 20 (Efficient sequential composition)**, Batra, Chen, Jain, Zhang, arXiv:2610.01421
(held version, sha256 8334c039…), p.58 (PDF p.60). Let QPT protocols `P_f` (in the `F`-hybrid) and
`P^f_g` (in the `f`-hybrid) realize `f` and `g` as in Definition 5, with simulator maps `sim_f`,
`sim_g`. Replace the at most `q(λ) ≤ poly(λ)` completed ideal-`f` calls of `P^f_g` by `P_f`
(fresh batches, fresh honest coins, fresh budget groups). Then `P^{P_f}_g` realizes `g` with
auxiliary-input-uniform QPT simulation; for every QPT adversary and test there are QPT induced
outer and call adversaries and tests with `Adv ≤ ν_g + q ν_f`, where `ν_g, ν_f` are the advantages
of the induced tests against `sim_g`, `sim_f`, uniform over admissible extensions and inputs; and
`ε^cor ≤ ε^cor_g + q ε^cor_f`.

**Formalization Note** (decision D11). Definition 6 (admissible reached states, fresh coins,
untouched reference, only the current batch accessible, retirement) holds by construction of the
execution semantics, so it is not a hypothesis. Calls are the `call` operations of the honest
controllers, with valid inputs; correctness is total variation from the ideal honest output
distribution, for honest devices with loss at most `q_dev`. -/
theorem theorem_20 (f g F : Func) (Pf Pg : Protocol) (Bf Bg : ℕ → ℕ → ℕ) (q pf pg : ℕ → ℕ)
    (hq : PolyBound q) (hPf : ResourceBound Pf pf) (hPg : ResourceBound Pg pg)
    (hcalls : ∀ lam x, (Pg.codeA lam x).CallsLE (q lam) ∧ (Pg.codeB lam x).CallsLE (q lam))
    (hvalid : ∀ lam x, (Pg.codeA lam x).CallsIn (f.validA lam) ∧
      (Pg.codeB lam x).CallsIn (f.validB lam))
    (simF : (A : Adversary Pf) → Simulator A) (simG : (A : Adversary Pg) → Simulator A)
    (hF : RealizesWith Pf F f (fun _ => True) Bf simF)
    (hG : RealizesWith Pg f g (fun _ => True) Bg simG) :
    ∃ simC : (A : Adversary (compose Pg Pf q)) → Simulator A,
      RealizesWith (compose Pg Pf q) F g (fun _ => True) (composeBudget Pg Pf q Bg Bf) simC ∧
      (∀ A : Adversary (compose Pg Pf q), A.IsQPT → ∀ nR : ℕ → ℕ, PolyBound nR →
        ∀ D : TestFam A nR, D.IsQPT →
          ∃ (Ag : Adversary Pg) (nRg : ℕ → ℕ) (Dg : TestFam Ag nRg) (Af : Adversary Pf)
            (nRf : ℕ → ℕ) (Df : TestFam Af nRf),
            Ag.corruptA = A.corruptA ∧ Af.corruptA = A.corruptA ∧ Ag.IsQPT ∧ Af.IsQPT ∧
            PolyBound nRg ∧ PolyBound nRf ∧ Dg.IsQPT ∧ Df.IsQPT ∧
            ∀ lam, advSup (compose Pg Pf q) F g (composeBudget Pg Pf q Bg Bf) A (simC A) D lam ≤
              advSup Pg f g Bg Ag (simG Ag) Dg lam + q lam * advSup Pf F f Bf Af (simF Af) Df lam) ∧
      ∀ (qd : ℝ) (εg εf : ℕ → ℝ), CorrectWithin Pg f g qd εg → CorrectWithin Pf F f qd εf →
        CorrectWithin (compose Pg Pf q) F g qd (fun lam => εg lam + q lam * εf lam) := by sorry

end DIObliviousTransfer
