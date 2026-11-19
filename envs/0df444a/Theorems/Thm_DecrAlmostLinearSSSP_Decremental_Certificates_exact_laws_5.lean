-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_5
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:13:30.264945+00:00
-- url     : https://prove2.me/theorems/d4974a71-55fc-4daa-a7a8-7a57436c4fd4
-- title:
--   Input capture, shortest walks and exact memory preparation
-- statement:
--   This collection gives the universally quantified contracts for input capture, shortest walks and exact memory preparation. All graph identifiers, queue keys, payloads, registers and addresses are finite natural indices; capacities and arithmetic registers use the scalar RAM types defined in the accompanying interface.
--
--   Input capture preserves the original graph tape while placing global parameters in reserved registers. The scalar shadow interpreter respects the source memory representation. Finite directed walks admit cycle erasure and minimum nonnegative-weight representatives. The exact-program memory layout separates public answers, adjacency data, active-edge flags, tentative labels, powers and trie storage; native clearing and allocation initialize these regions with their stated charged costs.
--
--   Each listed contract holds for every state and parameter tuple satisfying its explicit representation and domain hypotheses. Together they assert
--
--   $$
--   \bigwedge_{j\in J} L_j,
--   $$
--
--   where $L_j$ are the component queue, execution, representation, frame and work contracts described above. The conjunction preserves their individual quantifiers; it adds no successful-execution or correctness assumption to the external graph input.
--
--   These contracts form a reusable verification interface for the charged exact-recomputation branch of the general-domain reduction. **Formalization Note** The conjunction is balanced to expose component contracts through short projections and keep verification jobs within the service's compilation limit.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, October 2026 submission #912, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf, p.4 unnumbered exact-recomputation reduction and p.18 scalar unit-cost arithmetic model. Component contracts verify the concrete native compiler, radix-trie queue, graph representation and Dijkstra implementation in DecrAlmostLinearSSSP_RAMFoundation.

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

theorem DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5 : (((((((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (a d : Nat),
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          DecrAlmostLinearSSSP.Decremental.ShadowRep base F
            (DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.store
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg d))
              c)
            (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.store a d)
              g)) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (a d : Nat),
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          DecrAlmostLinearSSSP.Decremental.ShadowRep base F
            (DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.storeN
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg d))
              c)
            (DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.storeN a d) g))) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        ∀ (a : Nat),
          have c1 :=
            DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg a) (DecrAlmostLinearSSSP.Decremental.shadowReg a))
              c;
          have c2 :=
            DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              c1;
          have c3 :=
            DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              c2;
          And (DecrAlmostLinearSSSP.Decremental.ShadowRep base F c3 g)
            (@Eq.{1} Nat (c3.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (pc work : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc, realReg := c.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) pc)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) work,
          realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
        { pc := pc, realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
          halted := g.halted, fault := g.fault, work := work }))) ∧ (((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (pc : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc, realReg := c.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) pc,
          realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
        { pc := pc, realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
          halted := g.halted, fault := g.fault, work := g.work }) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    DecrAlmostLinearSSSP.Decremental.ShadowRep base F
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
      { pc := g.pc, realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
        halted := Bool.true, fault := g.fault, work := g.work })) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (a b : Nat),
        Iff
          (@LT.lt.{0} Nat instLTNat (c.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg a))
            (c.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg b)))
          (@LT.lt.{0} Nat instLTNat (g.natReg a) (g.natReg b))) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (a b : Nat),
      Iff
        (@LT.lt.{0} Real Real.instLT (c.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg a))
          (c.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg b)))
        (@LT.lt.{0} Real Real.instLT (g.realReg a) (g.realReg b))) ∧ (∀ {B F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep B F c g →
    DecrAlmostLinearSSSP.Decremental.ShadowRep B F (DecrAlmostLinearSSSP.Decremental.Structured.data c).machine g))))) ∧ ((((∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  DecrAlmostLinearSSSP.Decremental.ShadowRep B F
      (DecrAlmostLinearSSSP.Decremental.instructionEffect a.instruction s.machine) g →
    DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F (a.effect s) g) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F
        { realReg := s.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
          realMem := s.realMem, natMem := s.natMem }
        {
          pc :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
          realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem, halted := g.halted,
          fault := g.fault,
          work :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (pc : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    ((DecrAlmostLinearSSSP.Decremental.Structured.natural (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))).seq
      (DecrAlmostLinearSSSP.Decremental.Structured.nadd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    { realReg := s.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      realMem := s.realMem, natMem := s.natMem }) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    ∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        ∃ a,
          And (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Instruction a.instruction tr)
            (And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom a)
                s (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (a.effect s))
              (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F (a.effect s)
                (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g)))))) ∧ (((∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (d a : Nat),
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
            (@Nat.cast.{0} Real Real.instNatCast F) →
          ∃ t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                ((DecrAlmostLinearSSSP.Decremental.Structured.cast (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                      (DecrAlmostLinearSSSP.Decremental.shadowReg a)).seq
                  (DecrAlmostLinearSSSP.Decremental.Structured.div (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                    (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t)
              (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t
                (DecrAlmostLinearSSSP.Decremental.instructionEffect
                  (DecrAlmostLinearSSSP.Decremental.Instruction.cast d a) g))) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        ∀ (a : Nat),
          ∃ t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                (DecrAlmostLinearSSSP.Decremental.Structured.sequence
                  (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
                    (DecrAlmostLinearSSSP.Decremental.Structured.nadd
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (DecrAlmostLinearSSSP.Decremental.shadowReg a) (DecrAlmostLinearSSSP.Decremental.shadowReg a))
                    (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
                      (DecrAlmostLinearSSSP.Decremental.Structured.nadd
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
                        (DecrAlmostLinearSSSP.Decremental.Structured.nadd
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                        (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd)))))
                s (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) t)
              (And (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t g)
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d factor q : Nat),
  @Ne.{1} Nat factor d →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q) s q
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg d)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (s.natReg factor))),
        realMem := s.realMem, natMem := s.natMem }) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d factor q : Nat),
  @Ne.{1} Nat factor d →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.structuredConstant d factor q) s
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (s.natReg factor)),
        realMem := s.realMem, natMem := s.natMem }) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    ∀ (d q : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.structuredConstant (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) q)
              s
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t)
            (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t
              (DecrAlmostLinearSSSP.Decremental.instructionEffect
                (DecrAlmostLinearSSSP.Decremental.Instruction.natural d q) g)))))))) ∧ (((((∀ (d factor q k : Nat),
  @Ne.{1} Nat d k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q) k) ∧ (∀ (d factor q k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q) k)) ∧ ((∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    ∀ (address value : Nat),
      (∀ (a : Nat),
          @Ne.{1} Nat address
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
        DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F
          { realReg := s.realReg, natReg := s.natReg, realMem := s.realMem,
            natMem := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address value }
          g) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    ∀ (k value : Nat),
      @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
        @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k →
          @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k →
            @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) k →
              (∀ (j : Nat), @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j) k) →
                DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F
                  { realReg := s.realReg,
                    natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg k value,
                    realMem := s.realMem, natMem := s.natMem }
                  g))) ∧ (((∀ (j k : Nat),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.appendStoreReport s
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (DecrAlmostLinearSSSP.Decremental.appendedReport s))) ∧ ((∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    (∀ (a : Nat),
        @Ne.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F (DecrAlmostLinearSSSP.Decremental.appendedReport s) g) ∧ ((∀ (start : Nat) (reports : List.{0} Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.ReportLog start reports s →
    DecrAlmostLinearSSSP.Decremental.ReportLog start
      (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
        (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) reports
        (@List.cons.{0} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@List.nil.{0} Nat)))
      (DecrAlmostLinearSSSP.Decremental.appendedReport s)) ∧ (∀ (B bank start : Nat) (reports : List.{0} Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  (∃ r,
      @Eq.{1} Nat start
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    DecrAlmostLinearSSSP.Decremental.ReportLog start reports s →
      ∀ (a : Nat),
        @Ne.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.InputCapture.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.InputCapture.result s)) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.InputCapture.code)) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
    (DecrAlmostLinearSSSP.Decremental.InputCapture.result
      (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p i)))) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.InputCapture.code
    (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.InputCapture.code
    (DecrAlmostLinearSSSP.Decremental.shadowReg j))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.InputCapture.result
            (DecrAlmostLinearSSSP.Decremental.Structured.data
              (DecrAlmostLinearSSSP.Decremental.initialMachine p i))).natReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg j))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.InputCapture.result
            (DecrAlmostLinearSSSP.Decremental.Structured.data
              (DecrAlmostLinearSSSP.Decremental.initialMachine p i))).realReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg j))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k) (offset : Nat),
  @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val i.k e)))
        offset)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepared s)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 234) (instOfNatNat (nat_lit 234)))) base →
      DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W) base
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepared s)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 234) (instOfNatNat (nat_lit 234)))) base →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.code s
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                (DecrAlmostLinearSSSP.Decremental.Exact.height
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)))
              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
            t)
          (And
            (DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W) base
              (DecrAlmostLinearSSSP.Decremental.Exact.height
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W))
              t)
            (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
              (∀ (address : Nat),
                Or (@LT.lt.{0} Nat instLTNat address base)
                    (@LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                        (DecrAlmostLinearSSSP.Decremental.Exact.height
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)))
                      address) →
                  @Eq.{1} Nat (t.natMem address) (s.natMem address))))))))))) ∧ ((((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.code k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Layout.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Layout.result s))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.Image
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        i.n i.k)
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.result s)) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.Exact.Layout.code))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 224) (instOfNatNat (nat_lit 224))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 226) (instOfNatNat (nat_lit 226))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 228) (instOfNatNat (nat_lit 228))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 230) (instOfNatNat (nat_lit 230))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 232) (instOfNatNat (nat_lit 232))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 234) (instOfNatNat (nat_lit 234))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Layout.code k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Layout.code k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Clear.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Clear.advanced s)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Clear.code k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Clear.code k))))) ∧ ((((∀ (base length : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290)))) base →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 292) (instOfNatNat (nat_lit 292))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length) →
          ∃ t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Clear.code s
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) length)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                t)
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length))
                (And
                  (∀ (a : Nat),
                    @LE.le.{0} Nat instLENat base a →
                      @LT.lt.{0} Nat instLTNat a
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length) →
                        @Eq.{1} Nat (t.natMem a) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                    (∀ (a : Nat),
                      Or (@LT.lt.{0} Nat instLTNat a base)
                          (@LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length) a) →
                        @Eq.{1} Nat (t.natMem a) (s.natMem a)))))) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n)) (@List.instMembership.{0} (Fin n))
        (@List.cons.{0} (Fin n) u
          (@List.map.{0, 0} (Fin k) (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g) es))
        w →
      ∃ fs,
        And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active w v fs)
          (And (@List.IsSuffix.{0} (Fin k) fs es)
            (@List.IsSuffix.{0} (Fin n)
              (@List.cons.{0} (Fin n) w
                (@List.map.{0, 0} (Fin k) (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g) fs))
              (@List.cons.{0} (Fin n) u
                (@List.map.{0, 0} (Fin k) (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g) es)))))) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∃ fs,
      And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v fs)
        (And (@List.Sublist.{0} (Fin k) fs es)
          (@List.Nodup.{0} (Fin n)
            (@List.cons.{0} (Fin n) u
              (@List.map.{0, 0} (Fin k) (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g) fs))))) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    ∃ es,
      And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es)
        (@LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin k) es) n)) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (p : Fin n → Real),
      @Eq.{1} Real
        (@List.sum.{0} Real Real.instAdd Real.instZero
          (@List.map.{0, 0} (Fin k) Real
            (fun e =>
              @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (p (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e))
                (p (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e)))
            es))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (p u) (p v)))))) ∧ (((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n}
  {es fs : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    @DecrAlmostLinearSSSP.Decremental.Walk n k g active v w fs →
      @DecrAlmostLinearSSSP.Decremental.Walk n k g active u w
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin k)) (List.{0} (Fin k)) (List.{0} (Fin k))
          (@instHAppendOfAppend.{0} (List.{0} (Fin k)) (@List.instAppend.{0} (Fin k))) es fs)) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    @Eq.{1} (List.{0} (Fin k)) es (@List.nil.{0} (Fin k)) → @Eq.{1} (Fin n) u v)) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active v w →
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u w) ∧ ((∀ {n k : Nat} (es : List.{0} (Fin k)),
  @LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin k) es) n →
    @Membership.mem.{0, 0} (List.{0} (Fin k)) (Finset.{0} (List.{0} (Fin k)))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (List.{0} (Fin k))) (List.{0} (Fin k))
        (@Finset.instSetLike.{0} (List.{0} (Fin k))))
      (DecrAlmostLinearSSSP.Decremental.shortEdgeLists n k) es) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (u v : Fin n),
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
        ∃ es,
          And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es)
            (And (@LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin k) es) n)
              (∀ (fs : List.{0} (Fin k)),
                @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v fs →
                  @LE.le.{0} Real Real.instLE
                    (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es))
                    (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w fs)))))))))) ∧ (((((∀ {k : Nat} (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (es : List.{0} (Fin k)),
      @Eq.{1} ENNReal
        (@List.sum.{0} ENNReal ENNReal.instAdd ENNReal.instZero
          (@List.map.{0, 0} (Fin k) ENNReal (fun e => ENNReal.ofReal (w e)) es))
        (ENNReal.ofReal (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es)))) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (w : Fin k → ENNReal),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.distance n k g active w u v)
        (@List.sum.{0} ENNReal ENNReal.instAdd ENNReal.instZero (@List.map.{0, 0} (Fin k) ENNReal w es)))) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (u v : Fin n),
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
        ∃ es,
          And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es)
            (And (@LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin k) es) n)
              (@Eq.{1} ENNReal
                (@DecrAlmostLinearSSSP.Decremental.distance n k g active (fun e => ENNReal.ofReal (w e)) u v)
                (ENNReal.ofReal (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat)
  (e : Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k),
  @LE.le.{0} Real Real.instLE
    (@Nat.cast.{0} Real Real.instNatCast (i.weight (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (DecrAlmostLinearSSSP.Decremental.scale j))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat)
  (e : Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k),
  @Eq.{1} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n)
    (@DecrAlmostLinearSSSP.Decremental.Digraph.tail (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
      (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph e)
    (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph
      (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat)
  (e : Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k),
  @Eq.{1} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n)
    (@DecrAlmostLinearSSSP.Decremental.Digraph.head (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
      (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph e)
    (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph
      (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat) (active : Finset.{0} (Fin i.k)) {u v : Fin i.n}
  {es : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k)},
  @DecrAlmostLinearSSSP.Decremental.Walk (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
      (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
      (DecrAlmostLinearSSSP.Decremental.scaleActive i j active) u v es →
    @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph active u v
      (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) (Fin i.k)
        (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j) es)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat) (active : Finset.{0} (Fin i.k)) {u v : Fin i.n}
  {es : List.{0} (Fin i.k)},
  @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph active u v es →
    (∀ (e : Fin i.k),
        @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
          @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.scale j))) →
      ∃ rs,
        And
          (@DecrAlmostLinearSSSP.Decremental.Walk (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
            (DecrAlmostLinearSSSP.Decremental.scaleActive i j active) u v rs)
          (@Eq.{1} (List.{0} (Fin i.k))
            (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) (Fin i.k)
              (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j) rs)
            es)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (e : Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k),
      And
        (@LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast (i.weight (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@Nat.cast.{0} Real Real.instNatCast ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))))
        (@LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@Nat.cast.{0} Real Real.instNatCast ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e)))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@Nat.cast.{0} Real Real.instNatCast (i.weight (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))
            (DecrAlmostLinearSSSP.Decremental.delta i j)))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (rs : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k)),
      And
        (@LE.le.{0} Real Real.instLE
          (@List.sum.{0} Real Real.instAdd Real.instZero
            (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) Real
              (fun e =>
                @Nat.cast.{0} Real Real.instNatCast (i.weight (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))
              rs))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@List.sum.{0} Real Real.instAdd Real.instZero
              (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) Real
                (fun e =>
                  @Nat.cast.{0} Real Real.instNatCast ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                rs))))
        (@LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@List.sum.{0} Real Real.instAdd Real.instZero
              (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) Real
                (fun e =>
                  @Nat.cast.{0} Real Real.instNatCast ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                rs)))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@List.sum.{0} Real Real.instAdd Real.instZero
              (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) Real
                (fun e =>
                  @Nat.cast.{0} Real Real.instNatCast (i.weight (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))
                rs))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast
                (@List.length.{0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) rs))
              (DecrAlmostLinearSSSP.Decremental.delta i j))))) ∧ (∀ {k : Nat} (w : Fin k → Nat) (es : List.{0} (Fin k)),
  @Eq.{1} ENNReal
    (@List.sum.{0} ENNReal ENNReal.instAdd ENNReal.instZero
      (@List.map.{0, 0} (Fin k) ENNReal
        (fun e =>
          @Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (w e))
        es))
    (ENNReal.ofReal
      (@List.sum.{0} Real Real.instAdd Real.instZero
        (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE
        (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
          (fun e =>
            @Nat.cast.{0} ENNReal
              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
              (i.weight e))
          u v)
        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
          (@instHMul.{0} ENNReal
            (@Distrib.toMul.{0} ENNReal
              (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
          (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
          (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
            (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
            u v))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) {u v : Fin i.n} {es : List.{0} (Fin i.k)},
      @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph active u v es →
        (∀ (e : Fin i.k),
            @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
              @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (DecrAlmostLinearSSSP.Decremental.scale j))) →
          @LE.le.{0} ENNReal ENNReal.instLE
            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
              (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                u v))
            (ENNReal.ofReal
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@List.sum.{0} Real Real.instAdd Real.instZero
                  (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e)) es))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                  (DecrAlmostLinearSSSP.Decremental.delta i j))))) ∧ (∀ {k : Nat} (w : Fin k → Nat) (es : List.{0} (Fin k)) (e : Fin k),
  @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (w e))
      (@List.sum.{0} Real Real.instAdd Real.instZero
        (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es)))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active u v →
        @LE.le.{0} ENNReal ENNReal.instLE
            (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (i.weight e))
              u v)
            (ENNReal.ofReal
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (DecrAlmostLinearSSSP.Decremental.scale j))) →
          ∃ d,
            And
              (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                d)
              (And
                (@Eq.{1} ENNReal
                  (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                    (fun e =>
                      @Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (i.weight e))
                    u v)
                  (ENNReal.ofReal d))
                (@LE.le.{0} ENNReal ENNReal.instLE
                  (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                    (@instHMul.{0} ENNReal
                      (@Distrib.toMul.{0} ENNReal
                        (@instDistribOfSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                    (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
                    (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                      (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                      (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                      (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
                      (fun e =>
                        @Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                      u v))
                  (ENNReal.ofReal
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast i.n) (DecrAlmostLinearSSSP.Decremental.delta i j))))))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (u v : Fin n),
  Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v) →
    @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w u v)
      (@Top.top.{0} ENNReal ENNReal.instTop))) ∧ ((∀ {k : Nat} (w : Fin k → Nat) (W : Nat),
  (∀ (e : Fin k), @LE.le.{0} Nat instLENat (w e) W) →
    ∀ (es : List.{0} (Fin k)),
      @LE.le.{0} Real Real.instLE
        (@List.sum.{0} Real Real.instAdd Real.instZero
          (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin k) es)) (@Nat.cast.{0} Real Real.instNatCast W))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (active : Finset.{0} (Fin i.k)) (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active i.source v →
        @Ne.{1} (Fin i.n) v i.source →
          ∃ d,
            And
              (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d)
              (And
                (@LE.le.{0} Real Real.instLE d
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Nat.cast.{0} Real Real.instNatCast i.n) (@Nat.cast.{0} Real Real.instNatCast i.W)))
                (@Eq.{1} ENNReal
                  (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                    (fun e =>
                      @Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (i.weight e))
                    i.source v)
                  (ENNReal.ofReal d)))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real)
  (B : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
    ∀ (u v : Fin n),
      And
        (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v))
        (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v) B))))))))) := by sorry
